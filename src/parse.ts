import {error} from './main.ts';
import {Token, TokenType} from './scan.ts';

export enum NodeType {
  PROGRAM,
  THEOREM,
  CONST,
  STRUCT,
  FUNCTION,
  PARAMETER,
  PRINT,
  ASSIGN,
  EXPR,
  LITERAL,
  FUNCTION_CALL,
  RETURN,
  ASSERT,
  STATEMENT,
}

export type Node =
  | Program
  | Theorem
  | Function
  | Const
  | Struct
  | Statement
  | Parameter
  | Print
  | Assign
  | Expr
  | Return
  | Assert;

export interface NodeMixin<T extends NodeType> {
  type: T;
}

export interface Program extends NodeMixin<NodeType.PROGRAM> {
  declarations: Declaration[];
}

type Declaration = Function | Theorem | Const | Struct;

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

export interface Parameter extends NodeMixin<NodeType.PARAMETER> {
  line: number;
  name: string;
  paramType: string;
}

interface Statement extends NodeMixin<NodeType.STATEMENT> {
  contents: Print | Assign | Assert | Return;
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

interface Assert extends NodeMixin<NodeType.ASSERT> {
  value: Expr;
}

type Expr = Literal | FunctionCall;

interface Literal extends NodeMixin<NodeType.LITERAL> {
  value: string;
}

interface FunctionCall extends NodeMixin<NodeType.FUNCTION_CALL> {
  name: string;
  arguments: Expr[];
}

export function parse(tokens: Token[]) {
  let current = 0;

  // program -> declaration* EOF
  function parseProgram(): Program {
    const declarations: Declaration[] = [];
    while (tokens[current].type !== TokenType.EOF) {
      declarations.push(parseDeclaration());
    }
    return {
      type: NodeType.PROGRAM,
      declarations,
    };
  }

  // declaration -> function | theorem | const | struct
  function parseDeclaration(): Declaration {
    if (tokens[current].type === TokenType.FUNCTION) {
      return parseFunction();
    } else if (tokens[current].type === TokenType.THEOREM) {
      return parseTheorem();
    } else if (tokens[current].type === TokenType.CONST) {
      return parseConst();
    } else if (tokens[current].type === TokenType.STRUCT) {
      return parseStruct();
    } else {
      throw error(
        tokens[current].line,
        `Expected function or theorem, got ${TokenType[tokens[current].type]}`
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
      throw error(
        tokens[current].line,
        `Const names must begin and end with '*', *like-this*, got ${name} instead`
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
    const {lexeme: name, line} = expect(TokenType.IDENTIFIER);
    expect(TokenType.COLON);
    const paramType = parseType();
    return {type: NodeType.PARAMETER, line, name, paramType};
  }

  // type -> IDENTIFIER
  function parseType(): string {
    return expect(TokenType.IDENTIFIER).lexeme;
  }

  // statement -> print | assign | return
  function parseStatement(): Statement {
    let contents: Statement['contents'];
    switch (tokens[current].type) {
      case TokenType.PRINT:
        contents = parsePrint();
        break;
      case TokenType.ASSERT:
        contents = parseAssert();
        break;
      case TokenType.IDENTIFIER:
        contents = parseAssign();
        break;
      case TokenType.RETURN:
        contents = parseReturn();
        break;
      default:
        throw error(
          tokens[current].line,
          `Expected a statement but got ${TokenType[tokens[current].type]}`
        );
    }
    return {
      type: NodeType.STATEMENT,
      contents,
      rest:
        tokens[current].type !== TokenType.RIGHT_BRACE
          ? null
          : parseStatement(),
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

  function parseExpressions() {
    const expressions: Expr[] = [];
    while (tokens[current].type !== TokenType.RIGHT_PAREN) {
      expressions.push(parseExpr());
      if (tokens[current].type === TokenType.COMMA) {
        expect(TokenType.COMMA);
      } else {
        break;
      }
    }
    return expressions;
  }

  function parseExpr(): Expr {
    if (tokens[current].type === TokenType.IDENTIFIER) {
      return {
        type: NodeType.VARIABLE,
        value: expect(TokenType.IDENTIFIER).lexeme,
      };
    } else {
      return {
        type: NodeType.LITERAL,
        value: parseLiteral(),
      };
    }
  }

  function parseLiteral() {
    switch (tokens[current].type) {
      case TokenType.NUMBER:
        return expect(TokenType.NUMBER).lexeme;
      case TokenType.STRING:
        return expect(TokenType.STRING).lexeme;
      case TokenType.TRUE:
        return expect(TokenType.TRUE).lexeme;
      case TokenType.FALSE:
        return expect(TokenType.FALSE).lexeme;
      case TokenType.NIL:
        return expect(TokenType.NIL).lexeme;
      default:
        throw error(
          tokens[current].line,
          `Unexpected token ${TokenType[tokens[current].type]}`
        );
    }
  }

  function expect(...types: TokenType[]): Token {
    if (types.includes(tokens[current].type)) {
      const token = tokens[current];
      current++;
      return token;
    }
    throw error(
      tokens[current].line,
      `Expected ${types.map(tt => TokenType[tt]).join(', ')} but found ${TokenType[tokens[current].type]}`
    );
  }

  return parseProgram();
}
