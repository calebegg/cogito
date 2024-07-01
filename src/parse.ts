import {error} from './main.ts';
import {Token, TokenType} from './scan.ts';

interface Program {
  declarations: Declaration[];
}

interface Declaration {
  function?: Function;
  theorem?: Theorem;
}

interface Function {
  name: string;
  parameters: Parameter[];
  body: Statement[];
  return: Return;
}

interface Theorem {
  name: string;
  parameters: Parameter[];
  body: Statement[];
  return: Return;
}

interface Parameter {
  name: string;
  type: string;
}

interface Statement {
  print?: Print;
  assign?: Assign;
}

interface Print {
  template: string;
  expressions: Expr[];
}

interface Assign {
  name: string;
  value: Expr;
}

interface Return {
  value: Expr;
}

interface Expr {
  left: Expr;
  right: Expr;
  operator: Token;
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
      declarations,
    };
  }

  // declaration -> function | theorem
  function parseDeclaration(): Declaration {
    if (tokens[current].type === TokenType.FUNCTION) {
      return {function: parseFunction()};
    } else if (tokens[current].type === TokenType.THEOREM) {
      return {theorem: parseTheorem()};
    } else {
      throw error(tokens[current].line, 'Expected function or theorem');
    }
  }

  // function -> 'function' IDENTIFIER '(' parameters* ')' '{' block* return '}'
  function parseFunction(): Function {
    expect(TokenType.FUNCTION);
    const name = expect(TokenType.IDENTIFIER).lexeme;
    return {
      name: name,
      parameters: [],
      body: [],
      return: {value: null as any},
    };
  }

  // theorem -> 'theorem' IDENTIFIER '(' (parameters ',')* ')' '{' statement* return '}'
  function parseTheorem(): Theorem {
    expect(TokenType.THEOREM);
    const name = expect(TokenType.IDENTIFIER).lexeme;
    expect(TokenType.LEFT_PAREN);
    const parameters: Parameter[] = [];
    while (true) {
      parameters.push(parseParameter());
      if (tokens[current].type === TokenType.COMMA) {
        expect(TokenType.COMMA);
      } else {
        break;
      }
    }
    expect(TokenType.RIGHT_PAREN);
    expect(TokenType.LEFT_BRACE);
    expect(TokenType.RIGHT_BRACE);
    return {
      name,
      parameters,
      body: [],
      return: {value: null as any},
    };
  }

  // parameter -> IDENTIFIER ':' type
  function parseParameter(): Parameter {
    const name = expect(TokenType.IDENTIFIER).lexeme;
    expect(TokenType.COLON);
    const type = parseType();
    return {name, type};
  }

  // type -> IDENTIFIER
  function parseType(): Type {
    return expect(TokenType.IDENTIFIER).lexeme;
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
