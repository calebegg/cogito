import {Statement, If, NodeType} from './parse.ts';

export function endsInReturn(root: Statement | If | null): boolean {
  if (!root) return false;
  switch (root.type) {
    case NodeType.IF:
      return endsInReturn(root.body) && endsInReturn(root.rest);
    case NodeType.STATEMENT:
      switch (root.contents.type) {
        case NodeType.RETURN:
          return true;
        case NodeType.ASSERT:
        case NodeType.ASSIGN:
        case NodeType.PRINT:
          return endsInReturn(root.rest);
        case NodeType.IF:
          return endsInReturn(root.rest) || endsInReturn(root.contents);
        default:
          root.contents satisfies never;
          throw new Error('Unreachable');
      }
  }
}
