import {parse} from './parse.ts';
import {print} from './print.ts';
import {TokenType, scan} from './scan.ts';

export function run(source: string) {
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
export function error(line: number, message: string) {
  hadError = true;
  return new Error(`[line ${line}]: ${message}`);
}

if (import.meta.main) {
  run(`
    const *eight* = 8;

    struct point(
      x: number,
      y: number,
    );

    function pretty-print-point (p: point) {
      print("[Point x=~x0 y=~x1]", p.x, p.y);
    }

    pretty-print-point(new point(x = 1/2, y = 3/2))

    function factorial(n: natural) {
      print("Factorializing ~x0", n);
      if (n == 0) {
        return 1;
      }
      return n * factorial(n - 1);
    }
    theorem |factorial > 0|(x: natural) {
      return factorial(x) > 0;
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
