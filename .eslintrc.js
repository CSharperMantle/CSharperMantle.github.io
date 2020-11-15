module.exports = {
  env: {
    browser: true,
    es2021: true,
    jquery: true
  },
  extends: [
    'eslint-config-standard'
  ],
  parserOptions: {
    ecmaVersion: 12
  },
  rules: {
  },
  plugins: [
    'html'
  ],
  globals: {
    gsap: 'readonly',
    CustomEase: 'readonly',
    CustomWiggle: 'readonly',
    AsyncScriptLoader: 'readonly'
  }
}
