import fs from 'fs';
import path from 'path';

const rootDir = 'build';

const regex = /(\bfrom\s+["']((\.|antlr4ts\/).*))(["'])/g;

const walk = dir => {
  fs.readdirSync(dir).forEach(file => {
    const filePath = path.join(dir, file);
    if (fs.statSync(filePath).isDirectory()) {
      walk(filePath);
    } else {
      if (path.extname(filePath) === '.js') {
        fs.readFile(filePath, 'utf8', (err, data) => {
          if (err) throw err;

          // Match data to regex and if matches get group 2
          const matches = data.match(regex);
          if (matches) {
            const imports = matches.map(m => [m, m.split(regex)[2]]);
            imports.forEach(([m, imp]) => {
              if (imp.endsWith('.js')) {
                return;
              }
              let newImport = imp + '.js';
              if (imp.startsWith('.')) {
                const absolutePath = path.join(path.dirname(filePath), imp);
                // Remove the build from the path
                const codePath = absolutePath.replace(rootDir + '/', '');
                // Test if codePath/index.js exists
                const indexFile = path.join(codePath, 'index.ts');
                if (fs.existsSync(indexFile)) {
                  newImport = imp + '/index.js';
                }
              }
              data = data.replace(m, m.replace(imp, newImport));
            });
            fs.writeFile(filePath, data, 'utf8', error => {
              if (error) throw error;
            });
          }
        });
      }
      // if (path.extname(filePath) === '.ts') {
      //   fs.readFile(filePath, 'utf8', (err, data) => {
      //     if (err) throw err;
      //
      //     // Match data to regex and if matches get group 2
      //     const matches = data.match(regex);
      //     if (matches) {
      //       const imports = matches.map(m => [m, m.split(regex)[2]]);
      //       imports.forEach(([m, imp]) => {
      //         if (imp.endsWith('.d.ts')) {
      //           return;
      //         }
      //         let newImport = imp + '.d.ts';
      //         if (imp.startsWith('.')) {
      //           const absolutePath = path.join(path.dirname(filePath), imp);
      //           // Remove the build from the path
      //           const codePath = absolutePath.replace(rootDir + '/', '');
      //           // Test if codePath/index.js exists
      //           const indexFile = path.join(codePath, 'index.ts');
      //           if (fs.existsSync(indexFile)) {
      //             newImport = imp + '/index.d.ts';
      //           }
      //         }
      //         data = data.replace(m, m.replace(imp, newImport));
      //       });
      //       fs.writeFile(filePath, data, 'utf8', error => {
      //         if (error) throw error;
      //       });
      //     }
      //   });
      // }
    }
  });
};

walk(rootDir);
