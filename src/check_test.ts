/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { assert } from 'https://deno.land/std@0.207.0/assert/mod.ts';
import { scan } from './scan.ts';
import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { Declaration, NodeType, Program } from './parse.ts';
import { parse } from './parse.ts';
import { endsInReturn } from './check.ts';

function getFirstBody(node: Program | Declaration) {
  if (node.type === NodeType.PROGRAM) {
    node = node.declarations[0];
  }
  switch (node.type) {
    case NodeType.MUTUAL:
      return getFirstBody(node.functions[0]);
    case NodeType.FUNCTION:
    case NodeType.THEOREM:
    case NodeType.MAIN:
      return node.body;
    case NodeType.CONST:
    case NodeType.STRUCT:
      throw new Error('No body');
    default:
      node satisfies never;
      throw new Error('Unreachable');
  }
}

Deno.test('check returns in some basic functions [positive]', () => {
  function test(source: string) {
    assert(endsInReturn(getFirstBody(parse(scan(source)))));
  }

  test(outdent`
      function foo(x: number) {
        return x == 1;
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
Deno.test('check returns in some basic functions [negative]', () => {
  function test(source: string) {
    assert(!endsInReturn(getFirstBody(parse(scan(source)))));
  }

  test(outdent`
    function foo(x: number) {
        assert(x > 0);
    }
  `);
  test(outdent`
    theorem |foo runs|(x: number) {
      y = x + 2;
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
    }
  `);
});
