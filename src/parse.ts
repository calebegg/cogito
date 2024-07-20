/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { error } from './main.ts';
import { Token, TokenType } from './scan.ts';

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

  function errorWhileParsing(msg: string) {
    return error(tokens[current].line, tokens[current].char, msg);
  }

  // program -> declaration* EOF
  function parseProgram(): Program {
    const declarations: Declaration[] = [];
    while (tokens[current].type !== TokenType.EOF) {
      declarations.push(parseDeclaration());
    }
    expect(TokenType.EOF);
    return {
      type: NodeType.PROGRAM,
      declarations,
    };
  }

  // declaration -> function | theorem | const | struct | main
  function parseDeclaration(): Declaration {
    if (tokens[current].type === TokenType.FUNCTION) {
      return parseFunction();
    } else if (tokens[current].type === TokenType.THEOREM) {
      return parseTheorem();
    } else if (tokens[current].type === TokenType.CONST) {
      return parseConst();
    } else if (tokens[current].type === TokenType.STRUCT) {
      return parseStruct();
    } else if (tokens[current].type === TokenType.MAIN) {
      return parseMain();
    } else if (tokens[current].type === TokenType.MUTUAL) {
      const functions = [];
      expect(TokenType.MUTUAL);
      expect(TokenType.LEFT_BRACE);
      while (tokens[current].type === TokenType.FUNCTION) {
        functions.push(parseFunction());
      }
      expect(TokenType.RIGHT_BRACE);
      return {
        type: NodeType.MUTUAL,
        functions,
      };
    } else if (tokens[current].type === TokenType.IMPORT) {
      expect(TokenType.IMPORT);
      const name = expect(TokenType.STRING).lexeme;
      let from;
      if (tokens[current].type === TokenType.FROM) {
        expect(TokenType.FROM);
        from = expect(TokenType.STRING).lexeme;
      }
      expect(TokenType.SEMICOLON);
      return {
        type: NodeType.IMPORT,
        name,
        from,
      };
    } else {
      throw errorWhileParsing(
        outdent`
          Expected a declaration, got ${TokenType[tokens[current].type]}
          Every top level expression must be a declaration. To have code
          that executes at the top level, introduce a 'main' declaration.
        `.trim(),
      );
    }
  }

  // function -> 'function' IDENTIFIER '(' parameters* ')' '{' statement* '}'
  function parseFunction(): Function {
    expect(TokenType.FUNCTION);
    const name = expect(TokenType.IDENTIFIER).lexeme;
    expect(TokenType.LEFT_PAREN);
    const parameters = parseParameters();
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.LEFT_BRACE);
    const body = parseStatement();
    expect(TokenType.RIGHT_BRACE);
    return {
      type: NodeType.FUNCTION,
      name: name,
      parameters,
      body,
    };
  }

  // theorem -> 'theorem' IDENTIFIER '(' (parameters ',')* ')' '{' statement* '}'
  function parseTheorem(): Theorem {
    expect(TokenType.THEOREM);
    const name = expect(TokenType.IDENTIFIER).lexeme;
    expect(TokenType.LEFT_PAREN);
    const parameters = parseParameters();
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.LEFT_BRACE);
    const body = parseStatement();
    expect(TokenType.RIGHT_BRACE);
    return {
      type: NodeType.THEOREM,
      name,
      parameters,
      body,
    };
  }

  // const -> 'const' IDENTIFIER '=' expr ';'
  function parseConst(): Const {
    expect(TokenType.CONST);
    const name = expect(TokenType.IDENTIFIER).lexeme;
    if (!name.startsWith('*') && !name.endsWith('*')) {
      throw errorWhileParsing(
        `Const names must begin and end with '*', *like-this*, got ${name} instead`,
      );
    }
    expect(TokenType.EQUAL);
    const value = parseExpr();
    expect(TokenType.SEMICOLON);
    return {
      type: NodeType.CONST,
      name,
      value,
    };
  }

  function parseStruct(): Struct {
    expect(TokenType.STRUCT);
    const name = expect(TokenType.IDENTIFIER).lexeme;
    expect(TokenType.LEFT_PAREN);
    const parameters = parseParameters();
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.SEMICOLON);
    return {
      type: NodeType.STRUCT,
      name,
      parameters,
    };
  }

  function parseParameters() {
    const parameters: Parameter[] = [];
    if (tokens[current].type != TokenType.RIGHT_PAREN) {
      while (true) {
        if (tokens[current].type == TokenType.RIGHT_PAREN) break;
        parameters.push(parseParameter());
        if (tokens[current].type === TokenType.COMMA) {
          expect(TokenType.COMMA);
        } else {
          break;
        }
      }
    }
    return parameters;
  }

  // parameter -> IDENTIFIER ':' type
  function parseParameter(): Parameter {
    const { lexeme: name, line, char } = expect(TokenType.IDENTIFIER);
    expect(TokenType.COLON);
    const paramType = parseType();
    return { type: NodeType.PARAMETER, line, char, name, paramType };
  }

  // type -> IDENTIFIER
  function parseType(): string {
    return expect(TokenType.IDENTIFIER).lexeme;
  }

  // statement -> print | assign | return | if | expr
  function parseStatement(): Statement {
    let contents: Statement['contents'];
    switch (tokens[current].type) {
      case TokenType.PRINT:
        contents = parsePrint();
        break;
      case TokenType.ASSERT:
        contents = parseAssert();
        break;
      case TokenType.IDENTIFIER: {
        if (tokens[current + 1].type === TokenType.EQUAL) {
          contents = parseAssign();
        } else {
          const expr = parseExpr();
          expect(TokenType.SEMICOLON);
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
      case TokenType.LEFT_PAREN:
        contents = parseAssign();
        break;
      case TokenType.RETURN:
        contents = parseReturn();
        break;
      case TokenType.IF:
        contents = parseIf();
        break;
      default:
        throw errorWhileParsing(
          `Expected a statement but got ${TokenType[tokens[current].type]}`,
        );
    }
    let rest;
    if (tokens[current].type === TokenType.RIGHT_BRACE) {
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
    expect(TokenType.PRINT);
    expect(TokenType.LEFT_PAREN);
    const template = expect(TokenType.STRING).lexeme;
    let expressions: Expr[];
    if (tokens[current].type === TokenType.RIGHT_PAREN) {
      expressions = [];
    } else {
      expect(TokenType.COMMA);
      expressions = parseExpressions();
    }
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.SEMICOLON);
    return {
      type: NodeType.PRINT,
      template,
      expressions,
    };
  }

  // assert -> 'assert' '(' expr ')' ';'
  function parseAssert(): Assert {
    expect(TokenType.ASSERT);
    expect(TokenType.LEFT_PAREN);
    const value = parseExpr();
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.SEMICOLON);
    return {
      type: NodeType.ASSERT,
      value,
    };
  }

  // return -> 'return' expr ';'
  function parseReturn(): Return {
    expect(TokenType.RETURN);
    const value = parseExpr();
    expect(TokenType.SEMICOLON);
    return {
      type: NodeType.RETURN,
      value,
    };
  }

  // assign -> IDENTIFIER '=' expr ';'
  // assign -> '(' ID (',' ID)* ','? ')' '=' expr ';'
  function parseAssign(): Assign | TupleAssign {
    if (tokens[current].type === TokenType.LEFT_PAREN) {
      expect(TokenType.LEFT_PAREN);
      const names = [expect(TokenType.IDENTIFIER).lexeme];
      while (tokens[current].type === TokenType.COMMA) {
        expect(TokenType.COMMA);
        names.push(expect(TokenType.IDENTIFIER).lexeme);
      }
      expect(TokenType.RIGHT_PAREN);
      expect(TokenType.EQUAL);
      const value = parseExpr();
      expect(TokenType.SEMICOLON);
      return {
        type: NodeType.TUPLE_ASSIGN,
        names,
        value,
      };
    } else {
      const name = expect(TokenType.IDENTIFIER).lexeme;
      expect(TokenType.EQUAL);
      const value = parseExpr();
      expect(TokenType.SEMICOLON);
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
    expect(TokenType.MAIN);
    expect(TokenType.LEFT_BRACE);
    const body = parseStatement();
    expect(TokenType.RIGHT_BRACE);
    return {
      type: NodeType.MAIN,
      body,
    };
  }

  function parseIf(): If | Else {
    let condition;
    const { line, char } = tokens[current];
    if (tokens[current].type === TokenType.IF) {
      expect(TokenType.IF);
      expect(TokenType.LEFT_PAREN);
      condition = parseExpr();
      expect(TokenType.RIGHT_PAREN);
    }
    expect(TokenType.LEFT_BRACE);
    const body = parseStatement();
    expect(TokenType.RIGHT_BRACE);
    let elseBranch = null;
    if (tokens[current].type === TokenType.ELSE) {
      expect(TokenType.ELSE);
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
      tokens[current].type !== TokenType.RIGHT_PAREN &&
      tokens[current].type !== TokenType.RIGHT_BRACKET
    ) {
      expressions.push(parseExpr());
      if (tokens[current].type === TokenType.COMMA) {
        expect(TokenType.COMMA);
      } else {
        break;
      }
    }
    return expressions;
  }

  function parseExpr(minPrec = 1): Expr {
    const opers = new Map<
      TokenType,
      { precidence: number; assoc: 'left' | 'right' }
    >(
      [
        [TokenType.SKINNY_ARROW, { precidence: 1, assoc: 'left' }],
        [TokenType.AMP_AMP, { precidence: 2, assoc: 'left' }],
        [TokenType.PIPE_PIPE, { precidence: 2, assoc: 'left' }],
        [TokenType.EQUAL_EQUAL, { precidence: 3, assoc: 'left' }],
        [TokenType.GREATER, { precidence: 3, assoc: 'left' }],
        [TokenType.GREATER_EQUAL, { precidence: 3, assoc: 'left' }],
        [TokenType.LESS, { precidence: 3, assoc: 'left' }],
        [TokenType.LESS_EQUAL, { precidence: 3, assoc: 'left' }],
        [TokenType.BANG_EQUAL, { precidence: 3, assoc: 'left' }],
        [TokenType.PLUS, { precidence: 4, assoc: 'left' }],
        [TokenType.MINUS, { precidence: 4, assoc: 'left' }],
        [TokenType.STAR, { precidence: 5, assoc: 'left' }],
        [TokenType.SLASH, { precidence: 5, assoc: 'left' }],
        [TokenType.STAR_STAR, { precidence: 6, assoc: 'right' }],
        [TokenType.DOT, { precidence: 7, assoc: 'left' }],
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
      if (metadata.assoc === 'left') {
        nextMinPrec++;
      }
      const right = parseExpr(nextMinPrec);
      if (operToken.type === TokenType.DOT) {
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
    if (tokens[current].type === TokenType.LEFT_BRACKET) {
      expect(TokenType.LEFT_BRACKET);
      const contents = parseExpressions();
      expect(TokenType.RIGHT_BRACKET);
      return {
        type: NodeType.LIST_LITERAL,
        contents,
      };
    }
    // '(' (expr ',')* expr ')'
    if (tokens[current].type === TokenType.LEFT_PAREN) {
      expect(TokenType.LEFT_PAREN);
      if (
        (tokens[current].type === TokenType.RIGHT_PAREN &&
          tokens[current + 1].type === TokenType.FAT_ARROW) ||
        (tokens[current].type === TokenType.IDENTIFIER &&
          tokens[current + 1].type === TokenType.COLON)
      ) {
        return parseLambda();
      }
      const inside = parseExpr();
      if (tokens[current].type === TokenType.COMMA) {
        const values = [inside];
        while (tokens[current].type === TokenType.COMMA) {
          expect(TokenType.COMMA);
          if (tokens[current].type === TokenType.RIGHT_PAREN) {
            break;
          }
          values.push(parseExpr());
        }
        expect(TokenType.RIGHT_PAREN);
        return {
          type: NodeType.TUPLE,
          values,
        };
      }
      expect(TokenType.RIGHT_PAREN);
      return inside;
    }
    if (tokens[current].type === TokenType.SWITCH) {
      return parseSwitch();
    }
    // Unary expressions
    if (tokens[current].type === TokenType.BANG) {
      expect(TokenType.BANG);
      const right = parseExpr();
      return {
        type: NodeType.FUNCTION_CALL,
        name: 'not',
        args: [right],
      };
    }
    if (tokens[current].type === TokenType.MINUS) {
      expect(TokenType.MINUS);
      const right = parseExpr();
      return {
        type: NodeType.FUNCTION_CALL,
        name: '-',
        args: [right],
      };
    }
    if (tokens[current].type === TokenType.DOT_DOT_DOT) {
      expect(TokenType.DOT_DOT_DOT);
      const right = parseExpr();
      return {
        type: NodeType.SPREAD,
        value: right,
        line: tokens[current].line,
        char: tokens[current].char,
      };
    }
    if (tokens[current].type === TokenType.NEW) {
      expect(TokenType.NEW);
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
    if (tokens[current].type === TokenType.IDENTIFIER) {
      const { lexeme } = expect(TokenType.IDENTIFIER);
      if (tokens[current].type === TokenType.LEFT_PAREN) {
        expect(TokenType.LEFT_PAREN);
        const args = parseExpressions();
        expect(TokenType.RIGHT_PAREN);
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
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.FAT_ARROW);
    // TODO: Support block bodies
    const body = parseExpr();
    return {
      type: NodeType.LAMBDA,
      parameters,
      body,
    };
  }

  function parseSwitch(): Switch {
    expect(TokenType.SWITCH);
    expect(TokenType.LEFT_PAREN);
    const value = parseExpr();
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.LEFT_BRACE);
    const cases = [];
    while (tokens[current].type == TokenType.CASE) {
      expect(TokenType.CASE);
      const value = parseExpr();
      expect(TokenType.COLON);
      const body = parseExpr();
      expect(TokenType.SEMICOLON);
      cases.push({
        value,
        body,
      });
    }
    let def;
    if (tokens[current].type === TokenType.DEFAULT) {
      expect(TokenType.DEFAULT);
      expect(TokenType.COLON);
      def = parseExpr();
      expect(TokenType.SEMICOLON);
    }
    expect(TokenType.RIGHT_BRACE);
    return { type: NodeType.SWITCH, value, cases, def };
  }

  function parseLiteral() {
    switch (tokens[current].type) {
      case TokenType.NUMBER:
        return expect(TokenType.NUMBER).literal!;
      case TokenType.STRING:
        return expect(TokenType.STRING).lexeme;
      case TokenType.TRUE:
        return expect(TokenType.TRUE).lexeme;
      case TokenType.FALSE:
        return expect(TokenType.FALSE).lexeme;
      case TokenType.NIL:
        return expect(TokenType.NIL).lexeme;
      default:
        throw errorWhileParsing(
          `Unexpected token ${TokenType[tokens[current].type]}`,
        );
    }
  }

  function expect(...types: TokenType[]): Token {
    if (types.includes(tokens[current].type)) {
      const token = tokens[current];
      current++;
      return token;
    }
    throw errorWhileParsing(
      `Expected ${types.map((tt) => TokenType[tt]).join(', ')} but found ${
        TokenType[tokens[current].type]
      }`,
    );
  }

  return parseProgram();
}
