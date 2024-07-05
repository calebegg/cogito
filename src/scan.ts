import {error} from './main.ts';

export enum TokenType {
  // Single-character tokens
  LEFT_PAREN,
  RIGHT_PAREN,
  LEFT_BRACE,
  RIGHT_BRACE,
  LEFT_BRACKET,
  RIGHT_BRACKET,
  COMMA,
  DOT,
  DOT_DOT_DOT,
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
  ASSERT,
  CONST,
  ELSE,
  FALSE,
  FUNCTION,
  IF,
  MAIN,
  NEW,
  NIL,
  PRINT,
  REDUCE,
  RETURN,
  STRUCT,
  THEOREM,
  TRUE,

  EOF,
}

const KEYWORDS = new Map([
  ['assert', TokenType.ASSERT],
  ['const', TokenType.CONST],
  ['else', TokenType.ELSE],
  ['false', TokenType.FALSE],
  ['function', TokenType.FUNCTION],
  ['if', TokenType.IF],
  ['main', TokenType.MAIN],
  ['new', TokenType.NEW],
  ['nil', TokenType.NIL],
  ['print', TokenType.PRINT],
  ['reduce', TokenType.REDUCE],
  ['return', TokenType.RETURN],
  ['struct', TokenType.STRUCT],
  ['theorem', TokenType.THEOREM],
  ['true', TokenType.TRUE],
]);

export interface Token {
  type: TokenType;
  lexeme: string;
  line: number;
  literal?: string;
}

export function scan(source: string): Token[] {
  const tokens: Token[] = [];
  let start = 0;
  let current = 0;
  let line = 1;

  function addToken(type: TokenType, literalMap = (x: string) => x) {
    tokens.push({
      type,
      lexeme: source.substring(start, current),
      line,
      literal: literalMap(source.substring(start, current)),
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
      case '[':
        addToken(TokenType.LEFT_BRACE);
        break;
      case ']':
        addToken(TokenType.RIGHT_BRACE);
        break;
      case ',':
        addToken(TokenType.COMMA);
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
      case '.':
        if (source.charAt(current) === '.') {
          if (source.charAt(current + 1) !== '.') {
            throw error(
              line,
              "'.' is an operator and '...' is an operator but '..' is not a thing"
            );
          }
          current += 2;
          addToken(TokenType.DOT_DOT_DOT);
        } else {
          addToken(TokenType.DOT);
        }
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
        addToken(TokenType.STRING);
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
        addToken(TokenType.IDENTIFIER);
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
          while (source.charAt(current).match(/[0-9_]/)) {
            current++;
          }
          if (source.charAt(current) === '/') {
            current++;
            while (source.charAt(current).match(/[0-9_]/)) {
              current++;
            }
          }
          addToken(TokenType.NUMBER, n => n.replaceAll(/_/g, ''));
          continue;
        }
        if (c.match(/[a-zA-Z_*]/)) {
          if (c === '*' && !source.charAt(current).match(/[a-zA-Z0-9_-]/)) {
            addToken(TokenType.STAR);
            continue;
          }
          while (source.charAt(current).match(/[a-zA-Z0-9_*-]/)) {
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
  return [...tokens, {type: TokenType.EOF, lexeme: '', line}];
}
