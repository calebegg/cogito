import {assertEquals} from 'https://deno.land/std@0.207.0/assert/mod.ts';
import {TokenType, scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';

Deno.test('scan a basic function', () => {
  assertEquals(
    scan(
      outdent`
        function foo(x: number) {
          return 1;
        }
      `
    ).map(t => t.type),
    [
      TokenType.FUNCTION,
      TokenType.IDENTIFIER,
      TokenType.LEFT_PAREN,
      TokenType.IDENTIFIER,
      TokenType.COLON,
      TokenType.IDENTIFIER,
      TokenType.RIGHT_PAREN,
      TokenType.LEFT_BRACE,
      TokenType.RETURN,
      TokenType.NUMBER,
      TokenType.SEMICOLON,
      TokenType.RIGHT_BRACE,
      TokenType.EOF,
    ]
  );
});
