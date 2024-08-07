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
  Return,
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
  ['is-empty', 'endp'],
  ['&&', 'and'],
  ['||', 'or'],
  ['->', 'implies'],
  ['**', 'expt'],
  ['is-even', 'evenp'],
]);

export function print(root: Program) {
  const frontMatter: string[] = [];
  const structTypes: string[] = [];
  return printNode(root);

  function addFrontMatter(fm: string) {
    if (!frontMatter.includes(fm)) {
      frontMatter.push(fm);
    }
  }

  function printNode(root: Node): string {
    switch (root.type) {
      case NodeType.PROGRAM: {
        const progOut = root.declarations.map((d) => printNode(d)).join('\n\n');
        return outdent`
        ${frontMatter.join('\n')}

        ${progOut}
      `;
      }
      case NodeType.IMPORT:
        return `(include-book ${root.name} ${
          root.from
            ? `:dir :${
              root.from.substring(1).substring(0, root.from.length - 2)
            }`
            : ''
        })`;
      case NodeType.MAIN:
        return printNode(root.body);
      case NodeType.MUTUAL:
        return outdent`
          (mutual-recursion
            ${root.functions.map((f) => printNode(f)).join('\n\n')}
          )
        `;
      case NodeType.THEOREM: {
        const constraints = root.parameters.map((p) =>
          printTypeConstraint(p, structTypes)
        ).join(
          ' ',
        );
        const body = printNode(root.body);
        if (root.parameters.length === 0) {
          return outdent`
            (defthm ${root.name}
              ${body})
          `;
        } else if (root.parameters.length === 1) {
          return outdent`
            (defthm ${root.name}
                (implies ${constraints}
                    ${body}))
          `;
        }
        return outdent`
          (defthm ${root.name}
              (implies (and ${constraints})
                  ${body}))
        `;
      }
      case NodeType.FUNCTION: {
        const returnTupleArity = Math.max(
          ...findReturns(root.body).map((r) =>
            r.value.type === NodeType.TUPLE ? r.value.values.length : 1
          ),
        );
        let defaultReturn;
        if (returnTupleArity === 1) {
          defaultReturn = 'nil';
        } else {
          defaultReturn = `(mv ${
            Array.from({ length: returnTupleArity }).fill('nil').join(' ')
          })`;
        }
        const constraints = root.parameters.map((p) =>
          printTypeConstraint(p, structTypes)
        ).join(
          ' ',
        );
        const params = root.parameters.map((p) => printNode(p)).join(' ');
        const measure = root.measure
          ? `:measure ${printNode(root.measure)}`
          : '';
        const body = printNode(root.body);
        if (root.parameters.length === 0) {
          return outdent`
            (defun ${root.name} ()
              ${measure ? `(declare (xargs ${measure}))` : ''}
              ${body})
          `;
        }
        if (root.parameters.length === 1) {
          return outdent`
            (defun ${root.name} (${params})
              (declare (xargs :guard ${constraints} ${measure}))
              (if (not ${constraints})
                ${defaultReturn}
                ${body}))
          `;
        }
        return outdent`
        (defun ${root.name} (${params})
          (declare (xargs :guard (and ${constraints}) ${measure}))
          (if (not (and ${constraints}))
            ${defaultReturn}
            ${body}))
        `;
      }
      case NodeType.CONST:
        return `(defconst ${root.name} ${printNode(root.value)})`;
      case NodeType.STRUCT:
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
          !root.rest &&
          root.contents.type !== NodeType.RETURN
        ) {
          rest = ' nil)';
        }
        if (root.contents.type === NodeType.FUNCTION_CALL) {
          return `(prog2$ ${printNode(root.contents)} ${rest}`;
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
      case NodeType.SWITCH:
        return `(cond ${
          root.cases.map(({ value, body }) =>
            `((equal ${printNode(root.value)} ${printNode(value)}) ${
              printNode(body)
            })`
          ).join('\n')
        }${root.def ? ` (t ${printNode(root.def)})` : ''})`;
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
              outdent`
                (defun$ cogito-reduce (xs fn init)
                  (declare (xargs :guard (and (true-listp xs) (true-listp fn) (equal (len (cadr fn)) 2))))
                  (if (endp xs)
                    init
                    (apply$ fn (list (first xs) (cogito-reduce (rest xs) fn init)))))
              `,
            );
            break;
          case 'cogito-map':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              outdent`
                (defun$ cogito-map (xs fn)
                  (declare (xargs :guard (and (true-listp xs) (true-listp fn) (equal (len (cadr fn)) 1))))
                  (if (endp xs)
                    xs
                    (cons
                      (apply$ fn (list (first xs)))
                      (cogito-map (rest xs) fn))))
              `,
            );
            break;
          case 'cogito-flat-map':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              outdent`
                (defun$ cogito-flat-map (xs fn)
                  (declare (xargs :guard (and (true-listp xs) (true-listp fn) (equal (len (cadr fn)) 1))))
                  (if (endp xs)
                    xs
                    (append
                      (apply$ fn (list (first xs)))
                      (cogito-flat-map (rest xs) fn))))
              `,
            );
            break;
          case 'cogito-filter':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              outdent`
                (defun$ cogito-filter (xs fn)
                  (declare (xargs :guard (and (true-listp xs) (true-listp fn) (equal (len (cadr fn)) 1))))
                  (if (endp xs)
                    xs
                    (let ((ys (cogito-filter (rest xs) fn)))
                      (if (apply$ fn (list (first xs))) (cons (first xs) ys) ys))))
              `,
            );
            break;
          case 'cogito-zip-with':
            addFrontMatter('(include-book "projects/apply/top" :dir :system)');
            addFrontMatter(
              outdent`
                (defun$ cogito-zip-with (xs ys fn)
                  (declare (xargs :guard (and (true-listp xs) (true-listp ys) (true-listp fn) (equal (len (cadr fn)) 2))))
                  (if (or (endp xs) (endp ys))
                    nil
                    (cons (apply$ fn (list (first xs) (first ys)))
                          (cogito-zip-with (rest xs) (rest ys) fn))))
              `,
            );
            break;
        }
        return `(${name} ${root.args.map((a) => printNode(a)).join(' ')})`;
      }
      case NodeType.DOT_ACCESS:
        return `(assoc '${root.right} ${printNode(root.left)})`;
      case NodeType.LIST_LITERAL:
        if (root.contents.length === 0) {
          return 'nil';
        }
        if (root.contents.every((c) => c.type !== NodeType.SPREAD)) {
          return `(list ${root.contents.map((c) => printNode(c)).join(' ')})`;
        }
        return `(append ${
          root.contents.map((c) => {
            if (c.type === NodeType.SPREAD) {
              return printNode(c.value);
            }
            return `(list ${printNode(c)})`;
          }).join(' ')
        })`;
      case NodeType.SPREAD:
        throw error(
          root.line,
          root.char,
          "Can't use the spread operator here.",
        );
      case NodeType.IF:
        throw new Error("Not callable with expressions of type 'IF'");
      case NodeType.ELSE:
        throw new Error("Not callable with expressions of type 'ELSE'");
      case NodeType.TUPLE:
        return `(mv ${root.values.map((v) => printNode(v)).join(' ')})`;
      case NodeType.LAMBDA:
        return outdent`
          (lambda$ (${root.parameters.map((p) => printNode(p)).join(' ')})
            (declare (xargs :guard (and ${
          root.parameters.map(
            (p) => printTypeConstraint(p, structTypes),
          ).join(' ')
        }))) ${printNode(root.body)})`;
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

  function findReturns(s: Statement): Return[] {
    const returns = [];
    const { contents } = s;
    if (contents.type === NodeType.RETURN) {
      returns.push(contents);
    }
    if (contents.type === NodeType.IF) {
      returns.push(...findReturns(contents.body));
      let next = contents.elseBranch;
      while (next) {
        returns.push(...findReturns(next.body));
        if (next.type === NodeType.IF) {
          next = next.elseBranch;
        } else if (next.type === NodeType.ELSE) {
          next = null;
        }
      }
    }
    if (s.rest) {
      returns.push(...findReturns(s.rest));
    }
    return returns;
  }
}
