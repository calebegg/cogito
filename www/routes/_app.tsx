/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { type PageProps } from '$fresh/server.ts';
export default function App({ Component }: PageProps) {
  return (
    <html lang='en'>
      <head>
        <meta charset='utf-8' />
        <meta name='viewport' content='width=device-width, initial-scale=1.0' />
        <title>Cogito</title>
        <link rel='preconnect' href='https://fonts.googleapis.com' />
        <link
          rel='preconnect'
          href='https://fonts.gstatic.com'
          crossorigin='crossorigin'
        />
        <link
          href='https://fonts.googleapis.com/css2?family=Fira+Code:wght@300..700&display=swap'
          rel='stylesheet'
        />
        <link rel='stylesheet' href='/styles.css' />
      </head>
      <body>
        <Component />
      </body>
    </html>
  );
}
