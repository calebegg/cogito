import {parse} from './parse.ts';
import {TokenType, scan} from './scan.ts';

export function run(source: string) {
  const tokens = scan(source);
  for (const token of tokens) {
    console.log(
      `${TokenType[token.type]}: ${token.lexeme} on line ${token.line}`
    );
  }
  if (hadError) return;
  console.log(parse(tokens));
  // Run the code
}

let hadError = false;
export function error(line: number, message: string) {
  hadError = true;
  return new Error(`[line ${line}]: ${message}`);
}

if (import.meta.main) {
  run(`
    theorem |foo runs|(x: natural) {
      return x == 3;
    }

    function foo() {
      print("hello, world! ~x0", 3/4);
      return true;
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
