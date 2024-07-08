/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { error } from './main.ts';
import {
  Else,
  If,
  Node,
  NodeType,
  Parameter,
  Program,
  Statement,
} from './parse.ts';
import { endsInReturn } from './check.ts';

const FUNCTION_NAMES = new Map([
  ['==', 'equal'],
  ['reduce', 'cogito-reduce'],
  ['map', 'cogito-map'],
  ['flat-map', 'cogito-flat-map'],
  ['zip-with', 'cogito-zip-with'],
  ['filter', 'cogito-filter'],
]);

export function print(root: Program) {
  const frontMatter: string[] = [];
  return printNode(root);

  function addFrontMatter(fm: string) {
    if (!frontMatter.includes(fm)) {
      frontMatter.push(fm);
    }
  }

  function printNode(root: Node): string {
    const structTypes: string[] = [];
    let parentDeclarationType: NodeType | null = null;

    switch (root.type) {
      case NodeType.PROGRAM: {
        const progOut = root.declarations.map((d) => printNode(d)).join('\n\n');
        return outdent`
        ${frontMatter.join('\n')}

        ${progOut}
      `;
      }
      case NodeType.MAIN:
        parentDeclarationType = root.type;
        return printNode(root.body);
      case NodeType.THEOREM:
        parentDeclarationType = root.type;
        return outdent`
        (defthm ${root.name}
            (implies (and ${
          root.parameters.map((p) => printTypeConstraint(p, structTypes)).join(
            ' ',
          )
        })
                ${printNode(root.body)}))`;
      case NodeType.FUNCTION:
        parentDeclarationType = root.type;
        // Returning 0 is...weird, but 'nil' fails (acl2-numberp return-value)
        // and so fails most measures.
        return outdent`
        (defun ${root.name} (${
          root.parameters.map((p) => printNode(p)).join(' ')
        })
          (declare (xargs :guard (and ${
          root.parameters.map((p) => printTypeConstraint(p, structTypes)).join(
            ' ',
          )
        })))
          (if (not (and ${
          root.parameters.map((p) => printTypeConstraint(p, structTypes)).join(
            ' ',
          )
        }))
            0
            ${printNode(root.body)}))
        `;
      case NodeType.CONST:
        parentDeclarationType = root.type;
        return `(defconst ${root.name} ${printNode(root.value)})`;
      case NodeType.STRUCT:
        parentDeclarationType = root.type;
        addFrontMatter('(include-book "std/util/defaggregate" :dir :system)');
        structTypes.push(root.name);
        return outdent`
        (std::defaggregate ${root.name}
          (${
          root.parameters.map((f) =>
            `(${f.name} ${printTypeConstraint(f, structTypes)})`
          ).join(' ')
        }))`;
      case NodeType.PARAMETER:
        return root.name;
      case NodeType.STATEMENT: {
        if (root.contents.type === NodeType.IF) {
          return printIf(root.contents, root.rest);
        }
        let rest = root.rest ? `\n${printNode(root.rest)})` : '';
        if (
          parentDeclarationType == NodeType.MAIN &&
          !root.rest &&
          root.contents.type !== NodeType.RETURN
        ) {
          rest = ' nil)';
        }
        return printNode(root.contents) + rest;
      }
      case NodeType.PRINT:
        return `(prog2$ (cw ${
          root.template.substring(0, root.template.length - 1)
        }~%" ${root.expressions.map((e) => printNode(e)).join(' ')})`;
      case NodeType.ASSERT:
        return `(assert$ ${printNode(root.value)}`;
      case NodeType.ASSIGN:
        return `(let ((${root.name} ${printNode(root.value)}))`;
      case NodeType.TUPLE_ASSIGN:
        return `(mv-let (${root.names.join(' ')}) ${printNode(root.value)}`;
      case NodeType.RETURN:
        return printNode(root.value);
      case NodeType.TERMINAL_VALUE:
        if (root.value === 'true') return 't';
        if (root.value === 'false') return 'nil';
        if (root.value === 'nil') return 'nil';
        return `${root.value}`;
      case NodeType.FUNCTION_CALL: {
        let name = root.name;
        if (FUNCTION_NAMES.has(name)) {
          name = FUNCTION_NAMES.get(name)!;
        }
        switch (name) {
          case 'cogito-reduce':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              '(defun cogito-reduce (xs fn init) (if (endp xs) init (apply$ fn (list (first xs) (cogito-reduce (rest xs) fn init)))))',
            );
            addFrontMatter('(defwarrant cogito-reduce)');
            break;
          case 'cogito-map':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              '(defun cogito-map (xs fn) (if (endp xs) xs (cons (apply$ fn (list (first xs))) (cogito-map (rest xs) fn)))))',
            );
            addFrontMatter('(defwarrant cogito-map)');
            break;
          case 'cogito-flat-map':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              '(defun cogito-flat-map (xs fn) (if (endp xs) xs (append (apply$ fn (list (first xs))) (cogito-flat-map (rest xs) fn)))))',
            );
            addFrontMatter('(defwarrant cogito-flat-map)');
            break;
          case 'cogito-filter':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              '(defun cogito-filter (xs fn) (if (endp xs) xs (let ((ys (cogito-filter (rest xs) fn))) (if (apply$ fn (list (first xs))) (cons (first xs) ys) ys))))',
            );
            addFrontMatter('(defwarrant cogito-filter)');
            break;
          case 'cogito-zip-with':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              '(defun cogito-zip-with (xs ys fn) (if (or (endp xs) (endp ys)) nil (cons (apply$ fn (list (first xs) (first ys))) (cogito-zip-with (rest xs) (rest ys) fn))))) ',
            );
            addFrontMatter('(defwarrant cogito-zip-with)');
            break;
        }
        return `(${name} ${root.args.map((a) => printNode(a)).join(' ')})`;
      }
      case NodeType.DOT_ACCESS:
        return `(assoc '${root.right} ${printNode(root.left)})`;
      case NodeType.LIST_LITERAL:
        // TODO: add spread
        return `(append ${
          root.contents.map((c) => `(list ${printNode(c)})`).join(' ')
        })`;
      case NodeType.SPREAD:
        return printNode(root.value);
      case NodeType.IF:
        throw new Error("Not callable with expressions of type 'IF'");
      case NodeType.ELSE:
        throw new Error("Not callable with expressions of type 'IF'");
      case NodeType.TUPLE:
        return `(mv ${root.values.map((v) => printNode(v)).join(' ')})`;
      case NodeType.LAMBDA:
        return `(lambda$ (${root.parameters.join(' ')}) ${
          printNode(root.body)
        })`;
      default:
        root satisfies never;
        throw new Error('Unreachable');
    }
  }

  function printIf(root: If | Else, rest: Statement | null): string {
    if (root.type == NodeType.ELSE) {
      const body = printNode(root.body);
      if (endsInReturn(root.body)) {
        return body;
      }
      if (!rest) {
        throw error(root.line, root.char, 'Every branch must return a value');
      }
      return body + printNode(rest);
    }
    if (!root.elseBranch && !rest) {
      throw error(root.line, root.char, 'Every branch must return a value');
    }
    return outdent`
    (if ${printNode(root.condition)}
        ${printNode(root.body)}
        ${endsInReturn(root.body) ? '' : printNode(rest!)}
        ${
      root.elseBranch ? printIf(root.elseBranch, rest) : printNode(rest!)
    })`;
  }

  function printTypeConstraint(parameter: Parameter, structTypes: string[]) {
    switch (parameter.paramType) {
      case 'natural':
        return `(natp ${parameter.name})`;
      case 'integer':
        return `(integerp ${parameter.name})`;
      case 'string':
        return `(stringp ${parameter.name})`;
      case 'list':
      case 'list<any>':
        return `(true-listp ${parameter.name})`;
      case 'number':
        return `(rationalp ${parameter.name})`;
      case 'state':
        return `(state-p ${parameter.name})`;
      case 'list<number>':
        return `(rational-listp ${parameter.name})`;
      case 'list<natural>':
        return `(nat-listp ${parameter.name})`;
      case 'list<string>':
        return `(string-listp ${parameter.name})`;
      case 'list<list>':
        return `(true-list-listp ${parameter.name})`;
      case 'any':
        return 't';
      default:
        if (structTypes.includes(parameter.paramType)) {
          return `(${parameter.paramType}-p ${parameter.name})`;
        }
        throw error(
          parameter.line,
          parameter.char,
          `Unknown parameter type ${parameter.paramType}`,
        );
    }
  }
}
