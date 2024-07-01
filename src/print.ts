import {error} from './main.ts';
import {Node, NodeType, Parameter} from './parse.ts';
import outdent from 'http://deno.land/x/outdent/mod.ts';

let indentLevel = 0;

export function print(root: Node): string {
  switch (root.type) {
    case NodeType.PROGRAM:
      return root.declarations.map(d => print(d)).join('\n\n');
    case NodeType.THEOREM:
      return `(defthm ${root.name})`;
    case NodeType.FUNCTION:
      indentLevel = 2;
      return outdent`
        (defun ${root.name} (${root.parameters.map(p => print(p)).join(' ')})
          (declare (xargs :guard (and ${root.parameters.map(p => printTypeConstraint(p)).join(' ')})))
          (if (not (and ${root.parameters.map(p => printTypeConstraint(p)).join(' ')}))
            nil
            ${root.body.map(b => print(b)).join('\n')}${')'.repeat(indentLevel)}
        `;
    case NodeType.PARAMETER:
      return root.name;
    case NodeType.PRINT:
      indentLevel++;
      return `(prog2$ (cw ${root.template.substring(0, root.template.length - 1)}~%" ${root.expressions.map(e => print(e)).join(' ')})`;
    case NodeType.ASSIGN:
      indentLevel++;
      return `(let ((${root.name} ${print(root.value)}))`;
    case NodeType.RETURN:
      return print(root.value);
    case NodeType.LITERAL:
      if (root.value === 'true') return 't';
      if (root.value === 'false') return 'nil';
      if (root.value === 'nil') return 'nil';
      return `${root.value}`;
    case NodeType.FUNCTION_CALL:
      return `(${root.name} ${root.arguments.map(a => print(a)).join(' ')})`;
    default:
      root satisfies never;
      throw new Error('Unreachable');
  }
}

function printTypeConstraint(parameter: Parameter) {
  switch (parameter.paramType) {
    case 'natural':
      return `(natp ${parameter.name})`;
    case 'string':
      return `(stringp ${parameter.name})`;
    case 'list':
      return `(true-listp ${parameter.name})`;
    default:
      throw error(parameter.line, `Unexpected type: ${parameter.paramType}`);
  }
}
