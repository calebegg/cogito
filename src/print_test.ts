import {scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import {parse} from './parse.ts';
import {print} from './print.ts';
import {assertSnapshot} from 'https://deno.land/std@0.224.0/testing/snapshot.ts';

Deno.test('parse a basic program', async t => {
  await assertSnapshot(
    t,
    print(
      parse(
        scan(
          outdent`
            function foo(x: number) {
              if (x == 0) {
                return 3;
              } else if (x == 1) {
                y = [1, 2, 3, ...y];
              } else {
                return x.y;
              }
              return (1, 2, 3);
            }

            theorem |foo works|(x: number) {
              return foo(x) > 0;
            }

            const *foo* = 1;

            struct foo(x: number, y: number);

            main {
              assert(3 > 2);
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
