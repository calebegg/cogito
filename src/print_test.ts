/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { scan } from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { parse } from './parse.ts';
import { print } from './print.ts';
import { assertSnapshot } from 'https://deno.land/std@0.224.0/testing/snapshot.ts';
import { assertThrows } from 'https://deno.land/std@0.207.0/assert/mod.ts';

Deno.test('print a basic program', async (t) => {
  await assertSnapshot(
    t,
    print(
      parse(
        scan(
          outdent`
            import "arithmetic-5/top" from "system";

            function foo(x: number) {
              if (x == 0) {
                x = reduce([1, 2, 3], (x: number, y: number) => x + y * 2, 0);
                return x;
              } else if (x == 1) {
                y = [1, 2 ** 3, 3, ...y];
              } else {
                return x.y;
              }
              return (1, 2, 3);
            }

            theorem |foo works|(x: number) {
              return foo(x) > 0;
            }

            const *foo* = 1;

            struct foo(x: list<number>, y: number);

            main {
              assert(3 > 2 -> t && nil);
              print("hi", true + false + nil == 3);
              (x, y) = foo(1);
              print("hello, ~x0!", "world");
            }
          `,
        ),
      ),
    ),
  );
});

Deno.test('works with struct types', async (t) => {
  await assertSnapshot(
    t,
    print(
      parse(
        scan(
          outdent`
            struct point(x: number, y: number);

            function foo(p: point) {
              return p.x + p.y;
            }
          `,
        ),
      ),
    ),
  );
});

Deno.test('works with switch', async (t) => {
  await assertSnapshot(
    t,
    print(
      parse(
        scan(
          outdent`
            function foo(x: number) {
              return switch (x) {
                case 1: "a";
                case 2: "b";
                default: "c";
              };
            }
          `,
        ),
      ),
    ),
  );
});

Deno.test('errors with a misplaced spread', () => {
  assertThrows(
    () =>
      print(
        parse(
          scan(
            outdent`
            function foo(x: list) {
              return ...x;
            }
          `,
          ),
        ),
      ),
    Error,
    `Can't use the spread operator`,
  );
});
