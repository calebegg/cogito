/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { useEffect, useState } from 'preact/hooks';
import { process } from '../../src/index.ts';
import { CodeMirror } from '../components/CodeMirror.tsx';

enum Tab {
  LISP,
  RAW_ACL2,
}

export function Try({ initialSource }: { initialSource: string }) {
  const [output, setOutput] = useState<string[]>([]);
  const [lisp, setLisp] = useState('');
  const [currentTab, setCurrentTab] = useState(Tab.RAW_ACL2);
  const [source, setSource] = useState(initialSource);
  const [error, setError] = useState(false);

  useEffect(() => {
    setError(false);
    const lispSource = process(source);
    let timeoutId: number | null = null;
    const ws = new WebSocket(`wss://acl2-jbhe53iwqa-uc.a.run.app/acl2`);
    setLisp(lispSource.data);
    if (lispSource.status === 'error') {
      setError(true);
      setOutput(['Parse error']);
    } else {
      setOutput([]);
      timeoutId = setTimeout(() => {
        ws.addEventListener('message', ({ data }) => {
          setOutput((o) => [...o, data]);
        });
        ws.addEventListener('error', () => {
          setOutput((o) => [...o, 'Unexpected socket error']);
        });
        ws.send(lispSource.data);
        timeoutId = null;
      }, source == initialSource ? 0 : 2500);
    }
    return () => {
      if (timeoutId) clearTimeout(timeoutId);
      if (ws.readyState === WebSocket.OPEN) ws.close();
      setOutput([]);
    };
  }, [source]);

  return (
    <div class='row-on-wide'>
      <div style={{ paddingTop: 36, flex: 1 }}>
        <CodeMirror
          initialValue={initialSource}
          onChange={(v) => setSource(v)}
        />
      </div>
      <div style={{ flex: '1' }}>
        <div style='display: flex' role='tablist'>
          <button
            role='tab'
            class={'tab ' + (currentTab === Tab.LISP ? 'current' : '')}
            onClick={() => setCurrentTab(Tab.LISP)}
          >
            Lisp source code
          </button>
          <button
            role='tab'
            class={'tab ' + (currentTab === Tab.RAW_ACL2 ? 'current' : '')}
            onClick={() => setCurrentTab(Tab.RAW_ACL2)}
          >
            Raw ACL2 output
          </button>
        </div>
        {currentTab === Tab.LISP
          ? (
            <pre
              style={{ whiteSpace: 'pre-wrap' }}
              role='tabpanel'
              class={error ? 'error' : ''}
            >{lisp}</pre>
          )
          : (
            <div role='tabpanel' style={{ overflow: 'auto', maxHeight: 400 }}>
              {output.map((o) => (
                <>
                  <pre>{o}</pre>
                  <hr />
                </>
              ))}
            </div>
          )}
      </div>
    </div>
  );
}
