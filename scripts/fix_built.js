import fs from "fs";
import path from "path";

const rootDir = 'build';

const walk = (dir) => {
  fs.readdirSync(dir).forEach((file) => {
    const filePath = path.join(dir, file);
    if (fs.statSync(filePath).isDirectory()) {
      walk(filePath);
    } else {
      if (path.extname(filePath) === '.js') {
        fs.readFile(filePath, 'utf8', (err, data) => {
          if (err) throw err;
          let result = data.replace(/(\bfrom\s+["']\..*)(["'])/g, '$1.js$2');
          result = result.replace(/(\bfrom\s+["'])antlr4ts\/.*(["'])/g, '$1antlr4$2');
          result = result.replace(/import \{ VocabularyImpl } from "antlr4";/g, 'import { VocabularyImpl } from "antlr4ts/VocabularyImpl.js";');
          result = result.replace(/import { AbstractParseTreeVisitor } from 'antlr4';/g, 'import { AbstractParseTreeVisitor } from "antlr4ts/tree/AbstractParseTreeVisitor.js";');
          fs.writeFile(filePath, result, 'utf8', (error) => {
            if (error) throw error;
          });
        });
      }
    }
  });
};

walk(rootDir);