/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { useEffect, useState } from 'preact/hooks';
import { process } from '../../src/index.ts';
import { CodeMirror } from '../components/CodeMirror.tsx';

const ws = new WebSocket(`wss://acl2-jbhe53iwqa-uc.a.run.app/acl2`);

export interface Acl2Response {
  Kind: string;
  Body: string;
}

export function Try({ initialSource }: { initialSource: string }) {
  const [output, setOutput] = useState('');
  const [source, setSource] = useState(initialSource);
  const [error, setError] = useState(false);

  useEffect(() => {
    setError(false);
    const acl2Source = process(source);
    let id = -1;
    if (acl2Source.status === 'error') {
      setError(true);
      setOutput(acl2Source.data);
    } else {
      setOutput(acl2Source.data);
      // setOutput('Loading...');
      // id = setTimeout(() => {
      //   ws.addEventListener('message', (e) => {
      //     const data = JSON.parse(e.data) as Acl2Response;
      //     setError(data.Kind === 'ERROR');
      //     setOutput(data.Body);
      //   }, { once: true });
      //   ws.send(acl2Source.data);
      // }, 1000);
    }
    return () => {
      clearTimeout(id);
      setOutput('');
    };
  }, [source]);

  return (
    <div style='display: flex; gap: 16px;'>
      <CodeMirror initialValue={initialSource} onChange={(v) => setSource(v)} />
      <div style={{ flex: '1' }}>
        <div>
          <div id='lisp-tab'>Generated Lisp source</div>
        </div>
        <textarea
          style={{ width: '100%', height: '100%' }}
          aria-labelledby='lisp-tab'
          readonly
          value={output}
          className={error ? 'error' : ''}
        />
      </div>
    </div>
  );
}
