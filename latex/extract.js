const fs = require('fs');
const COMMENT = 'comment';
const CODE = 'code';
const deepEqual = (a, b) => {
    try {require('assert').deepStrictEqual(a,b); return true;}
    catch (e){ return false;}
};


const DEBUG = process.env.DEBUG == 'true';

let matchList = (l, cons, nil) =>
    l.length ? cons(l[0], l.slice(1)) : nil();

let span = (f, l) =>
    matchList( l
	     , (hd, tl) => {
		 if (f(hd)){
		     let [left, right] = span(f, tl);
		     return [[hd,...left], right]
		 }else
		     return [[], l];
	     }
	     , () => [ [],[] ]
    );

let groupBy = (f, l) =>
    matchList( l
	     , (hd, tl) => {
		 let [left, right] = span(f.bind(null, hd), tl);
		 return [[hd,...left], ...groupBy(f, right)];
	     }
	     , () => []
    )


function memoize(f, cache = {}, toKey = args => JSON.stringify(args)){
    return (...args) => {
	let key = toKey(...args);
	return cache[key] || (cache[key]=f(...args));
    };
}

let isDecl = b => {
    let k = b.k || b || '';
    return typeof k == "string" && k.startsWith('decl');
};

let nameOfLine = line => 
   (line.match(/^(?:(?:noeq|private|instance|assume|class|unfold|irreducible|val|let|type|rec) )+(?:\( *)?([^ :()]+)/) || [])[1];

let DIRS_PATH = [];
let DIRNAME_OF_MODULE = {};
let VIRTUAL_FS = {};
function readModuleSync(module, dirs = DIRS_PATH) {
    // let dirs = ['src/core', 'src/app', 'latex'].map(dir => DIR + dir + '/');
    if(VIRTUAL_FS[module]){
	let {content, path} = VIRTUAL_FS[module];
	DIRNAME_OF_MODULE[module] = path;
	return content;
    }
    let ex;
    for (let dir of dirs)
	try {
	    let path = dir+'/';
	    DIRNAME_OF_MODULE[module] = path;
	    return fs.readFileSync(path+module+'.fst');
	} catch (e) {ex=e;};
    throw `Module "${module}" was not found in directories ${dirs}`;
};

function parseModuleM(m){
    let blocks = readModuleSync(m).toString().split(/\n/);
    let kind = b => {
	if(b.startsWith('//@'))
	    return 'annot';
	if(b.startsWith('//!'))
	    return 'cmd';
	let slashes = (b.match(/^\/+/) || [])[0];
	if(slashes)
	    return slashes.length;
	if(b.match(/^(noeq|private|instance|assume|class|unfold|irreducible|val|let|type|rec)/)){
	    if(b.match(/^((noeq|private|instance|assume|class|unfold|irreducible|type|rec) )*val/))
		return 'decl-val';
	    return 'decl';
	}if(b.match(/^\#/))
	    return 'hash';
	if(b.match(/^(open|module)/))
	    return 'open';
	if(b.trim() == '')
	    return 'empty';
	return undefined;
    };
    blocks = groupBy((x, y) => {
	let xk = kind(x);
	let yk = kind(y);
	// console.error({x,y, xk, yk});
	return xk != 'annot'
	    && (
		(xk==yk && !isDecl(xk))
		|| (xk == 'decl-val' && yk == 'decl' && nameOfLine(x) == nameOfLine(y))
		|| yk == undefined
	    );
    }, blocks);
    blocks = blocks.filter(x => x.filter(x => x.trim()).length);
    blocks = blocks.map(s => ({s, k: kind(s[0]), parents: [m]}));
    for(let b of blocks){
	if(typeof b.k == 'number'){
	    b.s = b.s.map(x => x.slice(b.k));
	    b.s = b.s.map(x => x[0]==' ' ? x.slice(1) : x);
	}else if (isDecl(b))
	    b.name = m + '.' + nameOfLine(b.s[0]);
    }
    for(let b of blocks){
	b.s = b.s.join('\n');
	if (b.k == 'cmd'){
	    b.s = b.s.slice(3).trim();
	}
    }
    return blocks;
}

let parseModule = memoize(parseModuleM);

// let setAnnotation = (key, value, o) => {
//     o.annots = o.annots || {};
//     o.annots[key] = value;
// };
// let getAnnotation = (key, o) => {
//     return (o.annots || {})[key];
// };
// let delAnnotation = (key, o) => {
//     o.annots = o.annots || {};
//     delete o.annots[key];
// };

let shown = {};
let deepClone = x => JSON.parse(JSON.stringify(x));
// let cc = 0;
let runCmd = block => {
    // if(cc > 100)
	// debugger;
    // console.log(block.s, cc);
    let [cmd, ...args] = block.s.split(' ');
    if (cmd == 'open'){
	if(args.length != 1){
	    console.error({args});
	    throw "[runCmd,open] invalid command: " + block.s;
	}
	let m = args[0];
	return parseModule(m).map(deepClone).map(b => {b.parents = [...block.parents, ...b.parents]; return b;});
    } else if (cmd == 'add-dir'){
	if(args.length == 0)
	    throw "[runCmd,add-dir] invalid command: " + block.s;
	let path_self = DIRNAME_OF_MODULE[block.parents.slice(-1)[0]];
	DIRS_PATH.push(...args.map(x => {
	    let y = x[0] == '/' ? x : path_self + '/' + x;
	    return require('path').resolve(y);
	}));
	return [];
    } else if (cmd == 'show'){
	if(args.length != 1)
	    throw "[runCmd,show] invalid command: " + block.s;
	let name = args[0].replace(/op_u(\d+)/g, (_,p) => String.fromCodePoint(p));
	let result = names.resolve(name);
	if(!result)
	    throw "[runCmd] cannot show '" + args[0] + "'";
	result = deepClone(result);
	result.parents = [...block.parents, ...result.parents];
	shown[result.name] = block.parents;
	if(result.annots){
	    delete result.annots['hide'];
	    delete result.annots['hide-because-shown-at-module'];
	}
	return [result];
    }
    return [block];
};

let filters = {
    annotateDecls: blocks => {
	let annots = [],  l = [];
	for(let b of blocks){
	    let {k, s} = b;
	    b.xxx = 1;
	    if(k == 'annot') annots.push(b);
	    else {
		if((isDecl(b) || b.k === 3) && annots.length){
		    let dico = Object.assign({}, b.annots || {});
		    for(let [k,...v] of annots.map(x => x.s.slice(3).split('=')))
			dico[k] = v.length ? v.join('=') : undefined;
		    l.push(Object.assign({annots: dico}, b));
		}else
		    l.push(...annots, b);
		annots = [];
	    }
	}
	return l;
    },
    runCommands: blocks =>
	blocks.map(b => b.k == 'cmd' ? runCmd(b) : [b]).flat()
}

let id = x => x;

let filter = (blocks, blacklist_ = []) => {
    // TODO: is runCmd mutating stuff? JSON.parse o JSON.stringify results in infinite loop
    let blocks0 = blocks;
    // let blocks = JSON.parse(JSON.stringify(blocks0));
    let blacklist = blacklist_ instanceof Array
	? (x => blacklist_.includes(x)) : blacklist_;
    for(let [name, filter] of Object.entries(filters))
	blacklist(name) || (blocks = filter(blocks, blacklist_));
    return deepEqual(blocks0, blocks) ? blocks0 : filter(blocks, blacklist_);
};

let names = {
    _resolve: m => {
	let blocks = filter(parseModule(m), ['runCommands']).filter(x => x.name);
	for(let block of blocks)
	    names._cache[block.name] = block;
    },
    _cache: {},
    resolve: name => {
	if(names._cache[name])
	    return names._cache[name];
	names._resolve(name.split('.').slice(0,-1).join('.'));
	return names._cache[name];
    }
}

let mkRegexp = (sep='|',flags='g',regexp=true) => (body, val, key, annots) => {
    let [needle, ...repl] = val.split(sep);
    repl = repl.join(sep);
    return body.replace(regexp ? new RegExp(needle, flags) : needle, (...r) => {
	let s = repl;
	for(let i=0; i<r.length; i++)
	    s = s.replace(new RegExp('\\$'+i, 'g'), r[i]);
	return s;
    });
};

let annotVerbs = {
    'signature-only': (body, val, key, annots) => {
	let lines = body.split('\n'), keep = [];
	for(let line of lines){
	    if(line.match(/((noeq|private|instance|assume|class|unfold|irreducible|val|type|rec) )*let/))
		break;
	    else
		keep.push(line);
	}
	return keep.join('\n');
    },
    regexp: mkRegexp(),
    'regexp\'': mkRegexp('-->>','g'),
    'replace': mkRegexp('|','g',false),
    eval: (body, val, key, annots) => {
	return eval(val) || body;
    },
    'todo': (body, val, key, annots, hookafter) => {
	// let f = hookafter.f;
	// hookafter.f = all => '//TODO: '+val+'\n'+f(all)+'}';
	// hookafter.f = all => '\\todo{'+val+'}{'+f(all)+'}';
	return '//TODO:' + val +'\n' + body;
    },
    'figure': (body, val, key, annots, hookafter) => {
	let f = hookafter.f;
	let [before, after] = val.split('|')
	hookafter.f = all => '\\begin{figure}'+before+'\n'+f(all)+'\n'+after+'\\end{figure}';
	return body;
    },
    '...': body =>  body.split('\n')[0]+' =!\\shortdots!',
    'let-as-val': body =>  body.replace('let', 'val').split('\n')[0],
};

let tex_env = 'fstarcode';
let possible_tex_env = new Set([tex_env]);
let set_tex_env = env => {
    possible_tex_env.add(env);
    tex_env = env;
};
function escapeRegExp(string) {
  return string.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); // $& means the whole matched string
}
function reRegroupEnv(){
    let mk = name => `\\\\end\\{${name}\\}\n%\n\\\\begin\\{${name}\\}\n`;
    let re = `(${[...possible_tex_env].map(escapeRegExp).map(mk).join('|')})`;
    return new RegExp(re, 'g');
}

let render = blocks => {
    let previousOne = {};
    let chunks = [];
    let hiddenBlocks = [];
    for(let block of blocks){
	if(isDecl(block)){
	    DEBUG && console.log('annots=', block.annots);
	    let annots = block.annots || {};
	    if('hide-because-shown-at-module' in annots){
		let target = annots['hide-because-shown-at-module'];
		if(!shown[block.name])
		    throw `hide-because-shown-at-module: '${block.name}' not shown`; 
		if(shown[block.name].includes(target))
		    continue;
		else
		    throw `hide-because-shown-at-module: cannot find '${target}' in ${JSON.stringify(shown[block.name])}`;
	    }
	    if('hide' in annots){
		if(!(typeof annots['hide'] == 'string'
		     && annots['hide'].startsWith('but shown as comment')))
		    hiddenBlocks.push(block);
		continue;
	    }
	    let body =
		('no-trim' in annots || (
		    !('trim' in annots) && typeof block.k == 'number'))
		? block.s : block.s.trim();
	    delete annots['offset-start-line'];
	    let hookafter = {f: body => `\\begin{${tex_env}}\n${body.replace(/%/g, '٪')}\n\\end{${tex_env}}`};
	    while(Object.keys(annots).length > 0){
		for(let [key, val] of Object.entries(annots)){
		    delete annots[key];
		    body = (annotVerbs[key] || (_ => {
			throw `Annot verb not found: ${key} (args ${val}), near ${block.name}`;
			return body;
		    }))(body, val, key, annots, hookafter);
		}
	    }
	    chunks.push(hookafter.f(body));
	} else if (block.k === 3){
	    let body = block.s;
	    body = body.replace('{{hidden-report}}', () => {
		let blocks = hiddenBlocks.map(b => {
		    if(b.parents.includes('MachineIntegers') || b.parents.includes('NumTC'))
			return;
		    let lines = b.s.split('\n').filter(x => !x.startsWith('//')).length;
		    return {name: b.name, lines};
		}).filter(x => x);
		hiddenBlocks = [];

		return "{\\tiny{}" +
                    blocks.map(({name, lines}) => `\\fcode{${name}}: ${lines} lines; `)
		    + `TOTAL: ${blocks.reduce((x, {lines}) => x+lines, 0)}}`;
		// return "\\begin{itemize}" +
                //     blocks.map(({name, lines}) => `\\item \\fcode{${name}}: ${lines} lines`)
		//     + `\\end{itemize} TOTAL: ${blocks.reduce((x, {lines}) => x+lines, 0)}`;
	    });
	    chunks.push(body);
	}
    }
    return chunks.map(chunk => chunk)
	.join('\n%\n')
	.replace(reRegroupEnv(), "")
	.replace(/\(\*@replace-newline:([^)]+)\*\) *\n/g, (_,r) => r)
	.replace(/`itv_equality`/g, '=')
	.replace(/=!=/g, '!\\notPropEq{}!');
};


let [nodeExecutablePath, scriptPath, ...rest_argv] = process.argv;

let help = () => {
    console.log(`Usage:
- node ${scriptPath} [--tex-env=env] inline "some F* code"
- node ${scriptPath} [--tex-env=env] path/to/module.fst[:def] [... [path/to/moduleN.fst[:defN]]]

By default, 'tex-env' is 'fstarcode'.
`);
    process.exit();
}

let tex_env_option = '--tex-env=';
function main(args){
    const {resolve, basename, dirname} = require('path');
    let parseModuleExpression = mExpr => {
	let [mainModulePath, defName, ...rest] = mExpr.split(':');
	if(rest.length)
	    throw `Module expression '${mExpr}' is incorrect, it has more than one colon.`;
	let path = resolve(mainModulePath);
	let moduleName = basename(path).replace(/\.fsti?$/, '');
	return { path: dirname(path),
		 moduleName,
		 definitions: (defName||'').split(',').filter(x => x)
	       };
    };
    try {
	if(args.length==0)
	    help();
	if(args[0].startsWith(tex_env_option))
	    set_tex_env(args.splice(0,1)[0].slice(tex_env_option.length));
	if(args[0]=="--inline" && args.length == 2){
	    VIRTUAL_FS['inline-module'] = {
		path: process.cwd(),
		content: args[1]
	    };
	    DIRS_PATH.push(process.cwd());
	    console.log(render(filter(parseModule('inline-module'))));
	}else if(args.length){
	    main(['--inline', `//!add-dir .` +
		  args.map(parseModuleExpression)
		  .map(({path, moduleName, definitions}) =>
		      ( DIRS_PATH.includes(path) || DIRS_PATH.push(path)
 		      , definitions.length ? definitions.map(d => `\n\n//!show ${moduleName}.${d}`)
		                           : [`\n\n//!open ${moduleName}`]
                      )).flat().join('')]);
	};
    }catch(e){
	console.log(e);
    }
}

main(rest_argv);


