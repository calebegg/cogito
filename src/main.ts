import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import {parse} from './parse.ts';
import {print} from './print.ts';
import {TokenType, scan} from './scan.ts';

let sourceCopy: string;

export function run(source: string) {
  sourceCopy = source;
  const tokens = scan(source);
  for (const token of tokens) {
    console.log(
      `${TokenType[token.type]}: ${token.lexeme} on line ${token.line}`
    );
  }
  if (hadError) return;
  const tree = parse(tokens);
  console.log(tree);
  if (hadError) return;
  console.log(print(tree));
}

let hadError = false;
export function error(line: number, char: number, message: string) {
  hadError = true;
  return new Error(
    `[line ${line}]: ${message}\n` +
      (sourceCopy ? sourceCopy.split('\n')[line - 1] + '\n' : '') +
      ' '.repeat(char - 1) +
      '^'
  );
}

if (import.meta.main) {
  run(outdent`
    function foo(x: number) {
      return (x == 1, x == 0);
    }

    main {
      (foo, bar) = foo(3);
    }
  `);
  //   run(`
  //   function foo() {
  //     print("hello, world! ~x0", 3/4);
  //     return true;
  //   }

  //   function factorial(n: natural) {
  //     if (n == 0) {
  //       return 1;
  //     }
  //     return n * factorial(n - 1);
  //   }

  //   theorem |foo runs| {
  //     return foo == true;
  //   }
  // `);
}
