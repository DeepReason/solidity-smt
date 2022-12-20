module.exports = {
  preset: 'ts-jest',
  testEnvironment: 'node',
  testRegex: '(/__tests__/.*|(\\.|/))\\.(test|spec)\\.[jt]sx?$',
  testPathIgnorePatterns: ['/node_modules/', '/build', '/integration/*'],
  modulePaths: ['src'],
  verbose: true,
};
