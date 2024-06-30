import {error} from './main.ts';

export enum TokenType {
  // Single-character tokens
  LEFT_PAREN,
  RIGHT_PAREN,
  LEFT_BRACE,
  RIGHT_BRACE,
  COMMA,
  DOT,
  MINUS,
  PLUS,
  SEMICOLON,
  COLON,
  SLASH,
  STAR,

  // One or two character tokens
  BANG,
  BANG_EQUAL,
  EQUAL,
  EQUAL_EQUAL,
  GREATER,
  GREATER_EQUAL,
  LESS,
  LESS_EQUAL,

  // Literals
  IDENTIFIER,
  STRING,
  NUMBER,

  // Keywords
  FUNCTION,
  THEOREM,
  IF,
  ELSE,
  TRUE,
  FALSE,
  NIL,
  RETURN,
  REDUCE,

  EOF,
}

const KEYWORDS = new Map([
  ['function', TokenType.FUNCTION],
  ['theorem', TokenType.THEOREM],
  ['if', TokenType.IF],
  ['else', TokenType.ELSE],
  ['true', TokenType.TRUE],
  ['false', TokenType.FALSE],
  ['nil', TokenType.NIL],
  ['return', TokenType.RETURN],
  ['reduce', TokenType.REDUCE],
]);

interface Token {
  type: TokenType;
  lexeme: string;
  literal: string | null;
  line: number;
}

export function scan(source: string) {
  const tokens: Token[] = [];
  let start = 0;
  let current = 0;
  let line = 1;

  function addToken(type: TokenType, literal?: string) {
    tokens.push({
      type,
      lexeme: source.substring(start, current),
      literal: literal ?? null,
      line,
    });
  }

  while (current < source.length) {
    start = current;
    const c = source.charAt(current);
    current++;
    switch (c) {
      case '(':
        addToken(TokenType.LEFT_PAREN);
        break;
      case ')':
        addToken(TokenType.RIGHT_PAREN);
        break;
      case '{':
        addToken(TokenType.LEFT_BRACE);
        break;
      case '}':
        addToken(TokenType.RIGHT_BRACE);
        break;
      case ',':
        addToken(TokenType.COMMA);
        break;
      case '.':
        addToken(TokenType.DOT);
        break;
      case '-':
        addToken(TokenType.MINUS);
        break;
      case '+':
        addToken(TokenType.PLUS);
        break;
      case ';':
        addToken(TokenType.SEMICOLON);
        break;
      case ':':
        addToken(TokenType.COLON);
        break;
      case '*':
        addToken(TokenType.STAR);
        break;
      case '!':
        if (source.charAt(current) === '=') {
          addToken(TokenType.BANG_EQUAL);
          current++;
        } else {
          addToken(TokenType.BANG);
        }
        break;
      case '=':
        if (source.charAt(current) === '=') {
          current++;
          addToken(TokenType.EQUAL_EQUAL);
        } else {
          addToken(TokenType.EQUAL);
        }
        break;
      case '<':
        if (source.charAt(current) === '=') {
          current++;
          addToken(TokenType.LESS_EQUAL);
        } else {
          addToken(TokenType.LESS);
        }
        break;
      case '>':
        if (source.charAt(current) === '=') {
          current++;
          addToken(TokenType.GREATER_EQUAL);
        } else {
          addToken(TokenType.GREATER);
        }
        break;
      case '/':
        if (source.charAt(current) === '/') {
          while (source.charAt(current) !== '\n' && current < source.length) {
            current++;
          }
        } else {
          addToken(TokenType.SLASH);
        }
        break;
      case '"':
        while (source.charAt(current) !== '"' && current < source.length) {
          if (source.charAt(current) === '\n') {
            line++;
          }
          current++;
        }
        if (current >= source.length) {
          error(line, 'Unterminated string.');
        }
        current++;
        addToken(TokenType.STRING, source.substring(start + 1, current - 1));
        break;
      case '|':
        while (source.charAt(current) !== '|' && current < source.length) {
          if (source.charAt(current) === '\n') {
            error(line, "Unexpected end of line while looking for '|'");
            break;
          }
          current++;
        }
        if (current >= source.length) {
          error(line, 'Unterminated identifier.');
        }
        current++;
        addToken(TokenType.IDENTIFIER, source.substring(start, current));
        break;
      case ' ':
      case '\r':
      case '\t':
        // Ignore whitespace.
        break;
      case '\n':
        line++;
        break;
      default:
        if (c.match(/[0-9]/)) {
          while (source.charAt(current).match(/[0-9]/)) {
            current++;
          }
          addToken(TokenType.NUMBER, source.substring(start, current));
          continue;
        }
        if (c.match(/[a-zA-Z_]/)) {
          while (source.charAt(current).match(/[a-zA-Z0-9_-]/)) {
            current++;
          }
          addToken(
            KEYWORDS.get(source.substring(start, current)) ??
              TokenType.IDENTIFIER
          );
          continue;
        }
        error(line, 'Unexpected character.');
        break;
    }
  }
  return tokens;
}
