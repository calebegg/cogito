import {assertEquals} from 'https://deno.land/std@0.207.0/assert/mod.ts';
import {scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import {parse} from './parse.ts';
import {print} from './print.ts';

function clean(s: string) {
  return s.replaceAll(/\s/g, ' ').trim;
}

Deno.test('print a basic function', () => {
  assertEquals(
    clean(
      print(
        parse(
          scan(
            outdent`
              function foo(x: number) {
                return 1;
              }
            `
          )
        )
      )
    ),
    clean(`
    (defun foo (x)
         (declare (xargs :guard (and (rationalp x))))
         (if (not (and (rationalp x)))
           0
           1)`)
  );
});
