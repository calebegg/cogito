import {error} from './main.ts';
import {Token, TokenType} from './scan.ts';

export enum NodeType {
  PROGRAM,
  THEOREM,
  FUNCTION,
  PARAMETER,
  PRINT,
  ASSIGN,
  EXPR,
  LITERAL,
  FUNCTION_CALL,
  RETURN,
}

export type Node =
  | Program
  | Theorem
  | Function
  | Parameter
  | Print
  | Assign
  | Expr
  | Return;

export interface NodeMixin<T extends NodeType> {
  type: T;
}

export interface Program extends NodeMixin<NodeType.PROGRAM> {
  declarations: Declaration[];
}

// TODO: change to type alias
type Declaration = Function | Theorem;

interface Function extends NodeMixin<NodeType.FUNCTION> {
  name: string;
  parameters: Parameter[];
  body: Statement[];
}

interface Theorem extends NodeMixin<NodeType.THEOREM> {
  name: string;
  parameters: Parameter[];
  // What happens if you do `cw` in a theorem??
  body: Statement[];
}

export interface Parameter extends NodeMixin<NodeType.PARAMETER> {
  line: number;
  name: string;
  paramType: string;
}

type Statement = Print | Assign;

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

  // declaration -> function | theorem
  function parseDeclaration(): Declaration {
    if (tokens[current].type === TokenType.FUNCTION) {
      return parseFunction();
    } else if (tokens[current].type === TokenType.THEOREM) {
      return parseTheorem();
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
    const body = parseBody();
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
    const body = parseBody();
    expect(TokenType.RIGHT_BRACE);
    return {
      type: NodeType.THEOREM,
      name,
      parameters,
      body,
    };
  }

  function parseParameters() {
    const parameters: Parameter[] = [];
    if (tokens[current].type != TokenType.RIGHT_PAREN) {
      while (true) {
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

  function parseBody(): Statement[] {
    const statements: Statement[] = [];
    while (tokens[current].type !== TokenType.RIGHT_BRACE) {
      statements.push(parseStatement());
    }
    return statements;
  }

  // statement -> print | assign | return
  function parseStatement(): Statement {
    if (tokens[current].type === TokenType.PRINT) {
      return parsePrint();
    } else if (tokens[current].type === TokenType.IDENTIFIER) {
      return parseAssign();
    } else if (tokens[current].type === TokenType.RETURN) {
      return parseReturn();
    } else {
      throw error(
        tokens[current].line,
        `Expected print, assign, or return, got ${TokenType[tokens[current].type]}`
      );
    }
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
