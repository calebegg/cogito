import {assertEquals} from 'https://deno.land/std@0.207.0/assert/mod.ts';
import {scan} from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import {NodeType, parse} from './parse.ts';

Deno.test('parse a basic function', () => {
  assertEquals(
    parse(
      scan(
        outdent`
          function foo(x: number) {
            return 1;
           }
        `
      )
    ),
    {
      type: NodeType.PROGRAM,
      declarations: [
        {
          type: NodeType.FUNCTION,
          name: 'foo',
          parameters: [
            {type: NodeType.PARAMETER, line: 1, name: 'x', paramType: 'number'},
          ],
          body: {
            type: NodeType.STATEMENT,
            contents: {
              type: NodeType.RETURN,
              value: {
                type: NodeType.TERMINAL_VALUE,
                value: '1',
              },
            },
            rest: null,
          },
        },
      ],
    }
  );
});
