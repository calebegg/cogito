/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  autocompletion,
  closeBrackets,
  closeBracketsKeymap,
  completionKeymap,
} from '@codemirror/autocomplete';
import { defaultKeymap } from '@codemirror/commands';
import {
  bracketMatching,
  defaultHighlightStyle,
  syntaxHighlighting,
} from '@codemirror/language';
import { EditorState } from '@codemirror/state';
import {
  drawSelection,
  EditorView,
  highlightActiveLine,
  keymap,
  lineNumbers,
} from '@codemirror/view';
import { useCallback, useEffect, useRef } from 'preact/hooks';

export function CodeMirror({
  initialValue,
  onChange,
}: {
  initialValue: string;
  onChange: (v: string) => void;
}) {
  const viewRef = useRef<EditorView | null>(null);

  useEffect(() => {
    if (!viewRef.current) return;
    viewRef.current.setState(getState());
  }, [initialValue, viewRef.current]);

  function getState() {
    return EditorState.create({
      doc: initialValue,
      extensions: [
        lineNumbers(),
        drawSelection(),
        syntaxHighlighting(defaultHighlightStyle, { fallback: true }),
        bracketMatching(),
        closeBrackets(),
        autocompletion(),
        highlightActiveLine(),
        keymap.of([
          ...closeBracketsKeymap,
          ...defaultKeymap,
          ...completionKeymap,
        ]),
      ],
    });
  }

  const refCallback = useCallback((ref: HTMLDivElement | null) => {
    if (!ref) {
      viewRef.current?.destroy();
      return;
    }
    viewRef.current = new EditorView({
      state: getState(),
      parent: ref,
      dispatch: (t) => {
        onChange(t.newDoc.toString());
        viewRef.current!.update([t]);
      },
    });
  }, []);

  return (
    <div
      ref={refCallback}
      style={{ height: '100%', flex: '1', overflowY: 'scroll' }}
      aria-label='Cogito editor'
    >
    </div>
  );
}
