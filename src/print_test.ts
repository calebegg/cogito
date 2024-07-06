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
          return 1;
        }

        theorem |foo works|(x: number) {
          return foo(x) > 0;
        }

        const *foo* = 1;

        struct foo(x: number, y: number);

        main {
          print("hello, world!");
        }
      `
        )
      )
    )
  );
});
