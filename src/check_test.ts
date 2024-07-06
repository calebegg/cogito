import {assert} from 'https://deno.land/std@0.207.0/assert/mod.ts';
import {scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import {NodeType, Program, parse} from './parse.ts';
import {endsInReturn} from './check.ts';

function getFirstBody(p: Program) {
  const firstDeclaration = p.declarations[0];
  switch (firstDeclaration.type) {
    case NodeType.FUNCTION:
    case NodeType.THEOREM:
    case NodeType.MAIN:
      return firstDeclaration.body;
    case NodeType.CONST:
    case NodeType.STRUCT:
      throw new Error('No body');
    default:
      firstDeclaration satisfies never;
      throw new Error('Unreachable');
  }
}

Deno.test('check returns in some basic functions', () => {
  function test(source: string) {
    assert(endsInReturn(getFirstBody(parse(scan(source)))));
  }

  test(outdent`
    function foo(x: number) {
      return x = 1;
    }
  `);
  test(outdent`
    theorem |foo runs|(x: number) {
      y = x + 2;
      return foo(y);
    }
  `);
  test(outdent`
    function complex(x: number) {
      if (x == 0) {
        return false;
      } else if (x == 1) {
        return true;
      } else {
        y = 100;
      }
      y = y / 2;
      return y;
    }
  `);
});
