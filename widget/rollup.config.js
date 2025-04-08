import { babel } from '@rollup/plugin-babel';
import commonjs from '@rollup/plugin-commonjs';
import { nodeResolve } from '@rollup/plugin-node-resolve';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';
import typescript from '@rollup/plugin-typescript';
import { glob } from 'glob';
import externalGlobals from 'rollup-plugin-external-globals';
import livereload from 'rollup-plugin-livereload';
import serve from 'rollup-plugin-serve';

const commonConfig = {
    output: {
        format: 'es',
        // Hax: apparently setting `global` makes some CommonJS modules work ¯\_(ツ)_/¯
        intro: 'const global = window;',
        sourcemap: 'inline',
        plugins: [],
    },
    external: ['react', 'react-dom', '@leanprover/infoview'],
    plugins: [
        babel({
            babelHelpers: 'bundled',
            presets: ['@babel/preset-react', '@babel/preset-typescript'],
            extensions: ['.js', '.jsx', '.ts', '.tsx'],
        }),
        nodeResolve({
            browser: true,
        }),
        commonjs({
            // In some cases the common.js plugin will hoist dynamic `require` calls for Node.js
            // modules which are not ever actually called into a global `import` which we cannot
            // resolve since we are running in a browser. So block all these from being hoisted.
            // Note: one alternative, https://github.com/FredKSchott/rollup-plugin-polyfill-node
            // does not seem to work.
            ignore: [
                'process',
                'events',
                'stream',
                'util',
                'path',
                'buffer',
                'querystring',
                'url',
                'string_decoder',
                'punycode',
                'http',
                'https',
                'os',
                'assert',
                'constants',
                'timers',
                'console',
                'vm',
                'zlib',
                'tty',
                'domain',
                'dns',
                'dgram',
                'child_process',
                'cluster',
                'module',
                'net',
                'readline',
                'repl',
                'tls',
                'fs',
                'crypto',
                'perf_hooks',
            ],
        }),
    ],
};

const previewConfig = {
    ...commonConfig,
    input: 'src/preview/preview.jsx',
    output: {
        ...commonConfig.output,
        file: 'dist/preview.js',
    },
    plugins: [
        ...commonConfig.plugins,
        typescript(),
        serve({
            port: 8000,
            contentBase: ['public', 'dist'],
        }),
        livereload(),
        replace({
            'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV),
            preventAssignment: true, // TODO delete when `true` becomes the default
        }),
        externalGlobals({
            react: 'window.React',
            'react-dom': 'window.ReactDOM',
        }),
    ],
};

/** @type {(_: any) => import('rollup').RollupOptions} */
export default (_cliArgs) => {
    const inputs = glob.sync('src/*.tsx');

    const isProduction =
        process.env.NODE_ENV && process.env.NODE_ENV === 'production';

    const configForInput = (fname) => {
        return {
            ...commonConfig,
            input: fname,
            output: {
                ...commonConfig.output,
                dir: '../.lake/build/js',
                sourcemap: isProduction ? false : 'inline',
                plugins: isProduction ? [terser()] : [],
                compact: isProduction,
            },
            plugins: [
                ...commonConfig.plugins,
                typescript({
                    sourceMap: isProduction,
                    outDir: '../.lake/build/js',
                    declaration: true,
                }),
                replace({
                    'typeof window': JSON.stringify('object'),
                    'process.env.NODE_ENV': JSON.stringify(
                        process.env.NODE_ENV
                    ),
                    preventAssignment: true, // TODO delete when `true` becomes the default
                }),
            ],
        };
    };

    // We need each widget module to be bundled into a standalone .js file.
    // By default, when building a number of modules,
    // Rollup will produce chunk.js files
    // containing code that is shared between the different modules,
    // so we do not get standalone files.
    // This is 'code splitting' and cannot be disabled:
    // https://github.com/rollup/rollup/issues/2756
    // The only way to avoid splitting is to return an array of configs
    // so that Rollup runs on each module separately.
    // Unfortunately, in conjunction with TS typechecking,
    // this rechecks all TS files when bundling each module,
    // resulting in a quadratic build.
    // Instead, we compile TS first with tsc,
    // and then bundle the JS outputs with Rollup.
    const cfgs = inputs.map(configForInput);
    if (!isProduction) {
        cfgs.push(previewConfig);
    }
    return cfgs;
};
