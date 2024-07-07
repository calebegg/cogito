import {scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import {parse} from './parse.ts';
import {assertSnapshot} from 'https://deno.land/std@0.224.0/testing/snapshot.ts';
import {assertThrows} from 'https://deno.land/std@0.207.0/assert/assert_throws.ts';

Deno.test('parse a basic program', async t => {
  await assertSnapshot(
    t,
    parse(
      scan(
        outdent`
        function foo(x: number,) {
          (x, y) = (y, x);
          list = [x, ...list, y];
          p = new point(2, 3);
          y = (p.x, p.y);
          return (1 + x + "hello") * !true / -3 < false >= nil;
        }

        theorem |foo works|(x: number) {
          x = reduce([1, 2, 3], (x, y) => x + y, 0);
          return foo(3,) > 0;
        }

        const *foo* = 1;

        struct baz(x: number, y: number);

        main {
          print("hello, ~x0!", "world");
        }
      `,
      ),
    ),
  );
});

Deno.test('two mains throws', () => {
  assertThrows(
    () =>
      parse(scan(`main { return foo(state); } main { return bar(state); }`)),
    Error,
    'Only one main',
  );
});

Deno.test('invalid const name throws', () => {
  assertThrows(
    () => parse(scan(`const FOO = 3;`)),
    Error,
    'must begin and end',
  );
});

Deno.test('top level code throws', () => {
  assertThrows(
    () => parse(scan(`foo();`)),
    Error,
    'Every top level expression',
  );
});

Deno.test('expression at body level throws', () => {
  assertThrows(
    () => parse(scan(`function foo() {3;}`)),
    Error,
    'Expected a statement',
  );
});

Deno.test('improper "new" throws', () => {
  assertThrows(
    () => parse(scan(`function foo() {x = new 1;}`)),
    Error,
    'must be function calls',
  );
});

Deno.test('unbalanced braces throws', () => {
  assertThrows(
    () => parse(scan(`function foo() }`)),
    Error,
    'Expected LEFT_BRACE but found RIGHT_BRACE',
  );
});

Deno.test('unreachable code throws', () => {
  assertThrows(
    () => parse(scan(`function foo() { return 1; x = 2; }`)),
    Error,
    'Unreachable',
  );
});
