/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { error } from './main.ts';
import { Token, TokenType as TT } from './scan.ts';

export enum NodeType {
  ASSERT,
  ASSIGN,
  CONST,
  DOT_ACCESS,
  ELSE,
  FUNCTION_CALL,
  FUNCTION,
  IF,
  IMPORT,
  LAMBDA,
  LIST_LITERAL,
  MAIN,
  MUTUAL,
  PARAMETER,
  PRINT,
  PROGRAM,
  RETURN,
  SPREAD,
  STATEMENT,
  STRUCT,
  SWITCH,
  TERMINAL_VALUE,
  THEOREM,
  TUPLE_ASSIGN,
  TUPLE,
}

export type Node =
  | Program
  | Declaration
  | Statement
  | Statement['contents']
  | Parameter
  | Expr;

export interface NodeMixin<T extends NodeType> {
  type: T;
}

export interface Program extends NodeMixin<NodeType.PROGRAM> {
  declarations: Declaration[];
}

export type Declaration =
  | Function
  | Theorem
  | Const
  | Struct
  | Main
  | Mutual
  | Import;

interface Main extends NodeMixin<NodeType.MAIN> {
  body: Statement;
}

interface Function extends NodeMixin<NodeType.FUNCTION> {
  name: string;
  parameters: Parameter[];
  measure?: Expr;
  body: Statement;
}

interface Theorem extends NodeMixin<NodeType.THEOREM> {
  name: string;
  parameters: Parameter[];
  // What happens if you do `cw` in a theorem??
  body: Statement;
}

interface Const extends NodeMixin<NodeType.CONST> {
  name: string;
  value: Expr;
}

interface Struct extends NodeMixin<NodeType.STRUCT> {
  name: string;
  parameters: Parameter[];
}

interface Mutual extends NodeMixin<NodeType.MUTUAL> {
  functions: Function[];
}

interface Import extends NodeMixin<NodeType.IMPORT> {
  name: string;
  from?: string;
}

export interface Parameter extends NodeMixin<NodeType.PARAMETER> {
  line: number;
  char: number;
  name: string;
  paramType: string;
}

export interface Statement extends NodeMixin<NodeType.STATEMENT> {
  contents:
    | Print
    | Assign
    | TupleAssign
    | Assert
    | Return
    | If
    | Else
    | FunctionCall;
  rest: Statement | null;
}

interface Print extends NodeMixin<NodeType.PRINT> {
  template: string;
  expressions: Expr[];
}

interface Return extends NodeMixin<NodeType.RETURN> {
  value: Expr;
}

interface Assign extends NodeMixin<NodeType.ASSIGN> {
  name: string;
  value: Expr;
}

interface TupleAssign extends NodeMixin<NodeType.TUPLE_ASSIGN> {
  names: string[];
  value: Expr;
}

interface Assert extends NodeMixin<NodeType.ASSERT> {
  value: Expr;
}

export interface If extends NodeMixin<NodeType.IF> {
  condition: Expr;
  body: Statement;
  elseBranch: If | Else | null;
  line: number;
  char: number;
}

export interface Else extends NodeMixin<NodeType.ELSE> {
  body: Statement;
  line: number;
  char: number;
}

type Expr =
  | DotAccess
  | FunctionCall
  | Lambda
  | ListLiteral
  | Spread
  | Switch
  | TerminalValue
  | Tuple;

interface DotAccess extends NodeMixin<NodeType.DOT_ACCESS> {
  left: Expr;
  right: string;
}

interface TerminalValue extends NodeMixin<NodeType.TERMINAL_VALUE> {
  value: string;
}

interface FunctionCall extends NodeMixin<NodeType.FUNCTION_CALL> {
  name: string;
  args: Expr[];
}

interface ListLiteral extends NodeMixin<NodeType.LIST_LITERAL> {
  contents: Expr[];
}

interface Spread extends NodeMixin<NodeType.SPREAD> {
  value: Expr;
  line: number;
  char: number;
}

interface Tuple extends NodeMixin<NodeType.TUPLE> {
  values: Expr[];
}

interface Lambda extends NodeMixin<NodeType.LAMBDA> {
  parameters: Parameter[];
  body: Expr;
}

export interface Switch extends NodeMixin<NodeType.SWITCH> {
  value: Expr;
  cases: Array<{ value: Expr; body: Expr }>;
  def?: Expr;
}

export function parse(tokens: Token[]) {
  let hasMain = false;
  let current = 0;

  function curr() {
    return tokens[current];
  }

  function errorWhileParsing(msg: string) {
    return error(tokens[current].line, tokens[current].char, msg);
  }

  // program -> declaration* EOF
  function parseProgram(): Program {
    const declarations: Declaration[] = [];
    while (curr().type !== TT.EOF) {
      declarations.push(parseDeclaration());
    }
    expect(TT.EOF);
    return {
      type: NodeType.PROGRAM,
      declarations,
    };
  }

  // declaration -> function | theorem | const | struct | main
  function parseDeclaration(): Declaration {
    if (curr().type === TT.FUNCTION) {
      return parseFunction();
    } else if (curr().type === TT.THEOREM) {
      return parseTheorem();
    } else if (curr().type === TT.CONST) {
      return parseConst();
    } else if (curr().type === TT.STRUCT) {
      return parseStruct();
    } else if (curr().type === TT.MAIN) {
      return parseMain();
    } else if (curr().type === TT.MUTUAL) {
      const functions = [];
      expect(TT.MUTUAL);
      expect(TT.LEFT_BRACE);
      while (curr().type === TT.FUNCTION) {
        functions.push(parseFunction());
      }
      expect(TT.RIGHT_BRACE);
      return {
        type: NodeType.MUTUAL,
        functions,
      };
    } else if (curr().type === TT.IMPORT) {
      expect(TT.IMPORT);
      const name = expect(TT.STRING).lexeme;
      let from;
      if (curr().type === TT.FROM) {
        expect(TT.FROM);
        from = expect(TT.STRING).lexeme;
      }
      expect(TT.SEMICOLON);
      return {
        type: NodeType.IMPORT,
        name,
        from,
      };
    } else {
      throw errorWhileParsing(
        outdent`
          Expected a declaration, got ${TT[curr().type]}
          Every top level expression must be a declaration. To have code
          that executes at the top level, introduce a 'main' declaration.
        `.trim(),
      );
    }
  }

  // function -> 'function' IDENTIFIER '(' parameters* ')' '{' statement* '}'
  function parseFunction(): Function {
    expect(TT.FUNCTION);
    const name = expect(TT.IDENTIFIER).lexeme;
    expect(TT.LEFT_PAREN);
    const parameters = parseParameters();
    expect(TT.RIGHT_PAREN);
    expect(TT.LEFT_BRACE);
    let measure;
    if (curr().type === TT.MEASURE) {
      expect(TT.MEASURE);
      expect(TT.LEFT_PAREN);
      measure = parseExpr();
      expect(TT.RIGHT_PAREN);
      expect(TT.SEMICOLON);
    }
    const body = parseStatement();
    expect(TT.RIGHT_BRACE);
    return {
      type: NodeType.FUNCTION,
      name: name,
      parameters,
      measure,
      body,
    };
  }

  // theorem -> 'theorem' IDENTIFIER '(' (parameters ',')* ')' '{' statement* '}'
  function parseTheorem(): Theorem {
    expect(TT.THEOREM);
    const name = expect(TT.IDENTIFIER).lexeme;
    expect(TT.LEFT_PAREN);
    const parameters = parseParameters();
    expect(TT.RIGHT_PAREN);
    expect(TT.LEFT_BRACE);
    const body = parseStatement();
    expect(TT.RIGHT_BRACE);
    return {
      type: NodeType.THEOREM,
      name,
      parameters,
      body,
    };
  }

  // const -> 'const' IDENTIFIER '=' expr ';'
  function parseConst(): Const {
    expect(TT.CONST);
    const name = expect(TT.IDENTIFIER).lexeme;
    if (!name.startsWith('*') && !name.endsWith('*')) {
      throw errorWhileParsing(
        `Const names must begin and end with '*', *like-this*, got ${name} instead`,
      );
    }
    expect(TT.EQUAL);
    const value = parseExpr();
    expect(TT.SEMICOLON);
    return {
      type: NodeType.CONST,
      name,
      value,
    };
  }

  function parseStruct(): Struct {
    expect(TT.STRUCT);
    const name = expect(TT.IDENTIFIER).lexeme;
    expect(TT.LEFT_PAREN);
    const parameters = parseParameters();
    expect(TT.RIGHT_PAREN);
    expect(TT.SEMICOLON);
    return {
      type: NodeType.STRUCT,
      name,
      parameters,
    };
  }

  function parseParameters() {
    const parameters: Parameter[] = [];
    if (curr().type != TT.RIGHT_PAREN) {
      while (true) {
        if (curr().type == TT.RIGHT_PAREN) break;
        parameters.push(parseParameter());
        if (curr().type === TT.COMMA) {
          expect(TT.COMMA);
        } else {
          break;
        }
      }
    }
    return parameters;
  }

  // parameter -> IDENTIFIER ':' type
  function parseParameter(): Parameter {
    const { lexeme: name, line, char } = expect(TT.IDENTIFIER);
    expect(TT.COLON);
    const paramType = parseType();
    return { type: NodeType.PARAMETER, line, char, name, paramType };
  }

  // type -> IDENTIFIER
  function parseType(): string {
    return expect(TT.IDENTIFIER).lexeme;
  }

  // statement -> print | assign | return | if | expr
  function parseStatement(): Statement {
    let contents: Statement['contents'];
    switch (curr().type) {
      case TT.PRINT:
        contents = parsePrint();
        break;
      case TT.ASSERT:
        contents = parseAssert();
        break;
      case TT.IDENTIFIER: {
        if (tokens[current + 1].type === TT.EQUAL) {
          contents = parseAssign();
        } else {
          const expr = parseExpr();
          expect(TT.SEMICOLON);
          if (expr.type === NodeType.FUNCTION_CALL) {
            contents = expr;
          } else {
            throw errorWhileParsing(
              `Unexpected expression of type ${
                NodeType[expr.type]
              }. Assign to a variable or return it.`,
            );
          }
        }
        break;
      }
      case TT.LEFT_PAREN:
        contents = parseAssign();
        break;
      case TT.RETURN:
        contents = parseReturn();
        break;
      case TT.IF:
        contents = parseIf();
        break;
      case TT.MEASURE:
        throw errorWhileParsing('Measures must be at the top of the function');
      default:
        throw errorWhileParsing(
          `Expected a statement but got ${TT[curr().type]}`,
        );
    }
    let rest;
    if (curr().type === TT.RIGHT_BRACE) {
      rest = null;
    } else {
      if (contents.type === NodeType.RETURN) {
        throw errorWhileParsing('Unreachable code');
      }
      rest = parseStatement();
    }
    return {
      type: NodeType.STATEMENT,
      contents,
      rest,
    };
  }

  // print -> 'print' '(' template expr* ')' ';'
  function parsePrint(): Print {
    expect(TT.PRINT);
    expect(TT.LEFT_PAREN);
    const template = expect(TT.STRING).lexeme;
    let expressions: Expr[];
    if (curr().type === TT.RIGHT_PAREN) {
      expressions = [];
    } else {
      expect(TT.COMMA);
      expressions = parseExpressions();
    }
    expect(TT.RIGHT_PAREN);
    expect(TT.SEMICOLON);
    return {
      type: NodeType.PRINT,
      template,
      expressions,
    };
  }

  // assert -> 'assert' '(' expr ')' ';'
  function parseAssert(): Assert {
    expect(TT.ASSERT);
    expect(TT.LEFT_PAREN);
    const value = parseExpr();
    expect(TT.RIGHT_PAREN);
    expect(TT.SEMICOLON);
    return {
      type: NodeType.ASSERT,
      value,
    };
  }

  // return -> 'return' expr ';'
  function parseReturn(): Return {
    expect(TT.RETURN);
    const value = parseExpr();
    expect(TT.SEMICOLON);
    return {
      type: NodeType.RETURN,
      value,
    };
  }

  // assign -> IDENTIFIER '=' expr ';'
  // assign -> '(' ID (',' ID)* ','? ')' '=' expr ';'
  function parseAssign(): Assign | TupleAssign {
    if (curr().type === TT.LEFT_PAREN) {
      expect(TT.LEFT_PAREN);
      const names = [expect(TT.IDENTIFIER).lexeme];
      while (curr().type === TT.COMMA) {
        expect(TT.COMMA);
        names.push(expect(TT.IDENTIFIER).lexeme);
      }
      expect(TT.RIGHT_PAREN);
      expect(TT.EQUAL);
      const value = parseExpr();
      expect(TT.SEMICOLON);
      return {
        type: NodeType.TUPLE_ASSIGN,
        names,
        value,
      };
    } else {
      const name = expect(TT.IDENTIFIER).lexeme;
      expect(TT.EQUAL);
      const value = parseExpr();
      expect(TT.SEMICOLON);
      return {
        type: NodeType.ASSIGN,
        name,
        value,
      };
    }
  }

  function parseMain(): Main {
    if (hasMain) {
      throw error(
        tokens[current].line,
        tokens[current].char,
        'Only one main declaration is allowed',
      );
    }
    hasMain = true;
    expect(TT.MAIN);
    expect(TT.LEFT_BRACE);
    const body = parseStatement();
    expect(TT.RIGHT_BRACE);
    return {
      type: NodeType.MAIN,
      body,
    };
  }

  function parseIf(): If | Else {
    let condition;
    const { line, char } = tokens[current];
    if (curr().type === TT.IF) {
      expect(TT.IF);
      expect(TT.LEFT_PAREN);
      condition = parseExpr();
      expect(TT.RIGHT_PAREN);
    }
    expect(TT.LEFT_BRACE);
    const body = parseStatement();
    expect(TT.RIGHT_BRACE);
    let elseBranch = null;
    if (curr().type === TT.ELSE) {
      expect(TT.ELSE);
      elseBranch = parseIf();
    }
    return condition
      ? {
        type: NodeType.IF,
        condition,
        body,
        elseBranch,
        line,
        char,
      }
      : {
        type: NodeType.ELSE,
        body,
        line,
        char,
      };
  }

  function parseExpressions() {
    const expressions: Expr[] = [];
    while (
      curr().type !== TT.RIGHT_PAREN &&
      curr().type !== TT.RIGHT_BRACKET
    ) {
      expressions.push(parseExpr());
      if (curr().type === TT.COMMA) {
        expect(TT.COMMA);
      } else {
        break;
      }
    }
    return expressions;
  }

  function parseExpr(minPrec = 1): Expr {
    const opers = new Map<
      TT,
      { precidence: number; assocRight?: true }
    >(
      [
        [TT.SKINNY_ARROW, { precidence: 1 }],
        [TT.AMP_AMP, { precidence: 2 }],
        [TT.PIPE_PIPE, { precidence: 2 }],
        [TT.EQUAL_EQUAL, { precidence: 3 }],
        [TT.GREATER, { precidence: 3 }],
        [TT.GREATER_EQUAL, { precidence: 3 }],
        [TT.LESS, { precidence: 3 }],
        [TT.LESS_EQUAL, { precidence: 3 }],
        [TT.BANG_EQUAL, { precidence: 3 }],
        [TT.PLUS, { precidence: 4 }],
        [TT.MINUS, { precidence: 4 }],
        [TT.STAR, { precidence: 5 }],
        [TT.SLASH, { precidence: 5 }],
        [TT.STAR_STAR, { precidence: 6, assocRight: true }],
        [TT.DOT, { precidence: 7 }],
      ],
    );

    let left: Expr = parseLeaf();
    while (true) {
      const operToken = tokens[current];
      const metadata = opers.get(operToken.type);
      if (!metadata) break;
      if (metadata.precidence < minPrec) break;
      expect(operToken.type);
      let nextMinPrec = metadata.precidence;
      if (!metadata.assocRight) {
        nextMinPrec++;
      }
      const right = parseExpr(nextMinPrec);
      if (operToken.type === TT.DOT) {
        if (right.type !== NodeType.TERMINAL_VALUE) {
          throw errorWhileParsing("Right side of a '.' must be an identifier");
        }
        left = { type: NodeType.DOT_ACCESS, left, right: right.value };
      } else {
        left = {
          type: NodeType.FUNCTION_CALL,
          name: operToken.lexeme,
          args: [left, right],
        };
      }
    }
    return left;
  }

  function parseLeaf(): Expr {
    // '[' expr* ']'
    if (curr().type === TT.LEFT_BRACKET) {
      expect(TT.LEFT_BRACKET);
      const contents = parseExpressions();
      expect(TT.RIGHT_BRACKET);
      return {
        type: NodeType.LIST_LITERAL,
        contents,
      };
    }
    // '(' (expr ',')* expr ')'
    if (curr().type === TT.LEFT_PAREN) {
      expect(TT.LEFT_PAREN);
      if (
        (curr().type === TT.RIGHT_PAREN &&
          tokens[current + 1].type === TT.FAT_ARROW) ||
        (curr().type === TT.IDENTIFIER &&
          tokens[current + 1].type === TT.COLON)
      ) {
        return parseLambda();
      }
      const inside = parseExpr();
      if (curr().type === TT.COMMA) {
        const values = [inside];
        while (curr().type === TT.COMMA) {
          expect(TT.COMMA);
          if (curr().type === TT.RIGHT_PAREN) {
            break;
          }
          values.push(parseExpr());
        }
        expect(TT.RIGHT_PAREN);
        return {
          type: NodeType.TUPLE,
          values,
        };
      }
      expect(TT.RIGHT_PAREN);
      return inside;
    }
    if (curr().type === TT.SWITCH) {
      return parseSwitch();
    }
    // Unary expressions
    if (curr().type === TT.BANG) {
      expect(TT.BANG);
      const right = parseExpr();
      return {
        type: NodeType.FUNCTION_CALL,
        name: 'not',
        args: [right],
      };
    }
    if (curr().type === TT.MINUS) {
      expect(TT.MINUS);
      const right = parseExpr();
      return {
        type: NodeType.FUNCTION_CALL,
        name: '-',
        args: [right],
      };
    }
    if (curr().type === TT.DOT_DOT_DOT) {
      expect(TT.DOT_DOT_DOT);
      const right = parseExpr();
      return {
        type: NodeType.SPREAD,
        value: right,
        line: tokens[current].line,
        char: tokens[current].char,
      };
    }
    if (curr().type === TT.NEW) {
      expect(TT.NEW);
      const right = parseExpr();
      if (right.type !== NodeType.FUNCTION_CALL) {
        throw error(
          tokens[current].line,
          tokens[current].char,
          'New expressions must be function calls',
        );
      }
      return right;
    }
    if (curr().type === TT.IDENTIFIER) {
      const { lexeme } = expect(TT.IDENTIFIER);
      if (curr().type === TT.LEFT_PAREN) {
        expect(TT.LEFT_PAREN);
        const args = parseExpressions();
        expect(TT.RIGHT_PAREN);
        return {
          type: NodeType.FUNCTION_CALL,
          name: lexeme,
          args,
        };
      }
      return {
        type: NodeType.TERMINAL_VALUE,
        value: lexeme,
      };
    } else {
      return {
        type: NodeType.TERMINAL_VALUE,
        value: parseLiteral(),
      };
    }
  }

  function parseLambda(): Lambda {
    const parameters = parseParameters();
    expect(TT.RIGHT_PAREN);
    expect(TT.FAT_ARROW);
    // TODO: Support block bodies
    const body = parseExpr();
    return {
      type: NodeType.LAMBDA,
      parameters,
      body,
    };
  }

  function parseSwitch(): Switch {
    expect(TT.SWITCH);
    expect(TT.LEFT_PAREN);
    const value = parseExpr();
    expect(TT.RIGHT_PAREN);
    expect(TT.LEFT_BRACE);
    const cases = [];
    while (curr().type == TT.CASE) {
      expect(TT.CASE);
      const value = parseExpr();
      expect(TT.COLON);
      const body = parseExpr();
      expect(TT.SEMICOLON);
      cases.push({
        value,
        body,
      });
    }
    let def;
    if (curr().type === TT.DEFAULT) {
      expect(TT.DEFAULT);
      expect(TT.COLON);
      def = parseExpr();
      expect(TT.SEMICOLON);
    }
    expect(TT.RIGHT_BRACE);
    return { type: NodeType.SWITCH, value, cases, def };
  }

  function parseLiteral() {
    switch (curr().type) {
      case TT.NUMBER:
        return expect(TT.NUMBER).literal!;
      case TT.STRING:
        return expect(TT.STRING).lexeme;
      case TT.TRUE:
        return expect(TT.TRUE).lexeme;
      case TT.FALSE:
        return expect(TT.FALSE).lexeme;
      case TT.NIL:
        return expect(TT.NIL).lexeme;
      default:
        throw errorWhileParsing(
          `Unexpected token ${TT[curr().type]}`,
        );
    }
  }

  function expect(...types: TT[]): Token {
    if (types.includes(curr().type)) {
      const token = tokens[current];
      current++;
      return token;
    }
    throw errorWhileParsing(
      `Expected ${types.map((tt) => TT[tt]).join(', ')} but found ${
        TT[curr().type]
      }`,
    );
  }

  return parseProgram();
}
