import {assertSnapshot} from 'https://deno.land/std@0.224.0/testing/snapshot.ts';
import {scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';

Deno.test('scan a basic function', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        function foo(x: number) {
          return 1;
        }
      `
    )
  );
});

Deno.test('scan a basic theorem', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        theorem |foo works|(x: number) {
          return foo(x) > 0
        }
      `
    )
  );
});

Deno.test('scan a basic main', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        main {
          print("hello, world!");
        }
      `
    )
  );
});

Deno.test('scan a basic const', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        const *foo* = 1_000_000;
      `
    )
  );
});

Deno.test('scan a basic struct', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        struct foo(x: number, y: number);
      `
    )
  );
});

Deno.test('scan a basic assert', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        assert(x > 0);
      `
    )
  );
});

Deno.test('scan a basic print', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        print("hello, world!");
      `
    )
  );
});

Deno.test('scan a basic return', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        return 1;
      `
    )
  );
});

Deno.test('scan a basic assign', async t => {
  await assertSnapshot(
    t,
    scan(
      outdent`
        x = 1;
      `
    )
  );
});
