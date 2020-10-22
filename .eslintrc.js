module.exports = {
  env: {
    browser: true,
    es2021: true,
    jquery: true,
  },
  extends: [
    'standard'
  ],
  parserOptions: {
    ecmaVersion: 12
  },
  rules: {
    "space-before-function-paren": "off",
    "semi": 1,
  },
  plugins: [
    'html'
  ]
}
