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
} from "@codemirror/autocomplete@6.17.0";
import { defaultKeymap } from "@codemirror/commands@6.6.0";
import {
  bracketMatching,
  defaultHighlightStyle,
  syntaxHighlighting,
} from "@codemirror/language@6.10.2";
import { EditorState } from "@codemirror/state@6.4.1";
import {
  drawSelection,
  EditorView,
  highlightActiveLine,
  keymap,
  lineNumbers,
} from "@codemirror/view@6.28.4";
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
      style={{ height: '100%', width: '100%', overflowY: 'scroll' }}
      aria-label='Cogito editor'
    >
    </div>
  );
}
