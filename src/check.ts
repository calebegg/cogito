/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { Else, If, NodeType, Statement } from './parse.ts';

export function endsInReturn(root: Statement | If | Else | null): boolean {
  if (!root) return false;
  switch (root.type) {
    case NodeType.IF:
      return endsInReturn(root.body) && endsInReturn(root.elseBranch);
    case NodeType.ELSE:
      return endsInReturn(root.body);
    case NodeType.STATEMENT:
      switch (root.contents.type) {
        case NodeType.RETURN:
          return true;
        case NodeType.ASSERT:
        case NodeType.ASSIGN:
        case NodeType.TUPLE_ASSIGN:
        case NodeType.PRINT:
        case NodeType.FUNCTION_CALL:
          return endsInReturn(root.rest);
        case NodeType.IF:
          return endsInReturn(root.rest) || endsInReturn(root.contents);
        case NodeType.ELSE:
          return endsInReturn(root.rest) || endsInReturn(root.contents);
        default:
          root.contents satisfies never;
          throw new Error('Unreachable');
      }
  }
}
