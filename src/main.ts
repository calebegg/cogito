import {TokenType, scan} from './scan.ts';

export function run(source: string) {
  for (const token of scan(source)) {
    console.log(
      `${TokenType[token.type]}: ${token.lexeme} on line ${token.line}`
    );
  }
  if (hadError) return;
  // Run the code
}

let hadError = false;
export function error(line: number, message: string) {
  hadError = true;
  throw new Error(`[line ${line}]: ${message}`);
}

if (import.meta.main) {
  run(`
    function foo() {
      print("hello, world!");
      return true;
    }

    function factorial(n: natural) {
      if (n == 0) {
        return 1;
      }
      return n * factorial(n - 1);
    }

    theorem |foo runs| {
      return foo == true;
    }
  `);
}
