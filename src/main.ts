/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { parse } from './parse.ts';
import { print } from './print.ts';
import { scan, TokenType } from './scan.ts';

let sourceCopy: string;

export function setSource(source: string) {
  sourceCopy = source;
}

export function run(source: string) {
  sourceCopy = source;
  const tokens = scan(source);
  for (const token of tokens) {
    console.log(
      `${TokenType[token.type]}: ${token.lexeme} on line ${token.line}`,
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
    `[line ${line}:${char}]: ${message}\n` +
      (sourceCopy ? sourceCopy.split('\n')[line - 1] + '\n' : '') +
      ' '.repeat(char - 1) +
      '^',
  );
}

if (import.meta.main) {
  run(outdent`
    struct point(x: number, y: number);

    main {
      print("hello, world!");
      print("~x0", reduce([1, 2, 3], (x, y) => x + y, 0));
      print("~x0", map([1, 2, 3], (x) => x + 1));
      print("~x0", flat-map([1, 2, 3], (x) => [x, x + 1]));
      return 0;
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
