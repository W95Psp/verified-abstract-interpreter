let caml_thread_initialize = (...args) => {
    // console.log('caml_thread_initialize', args);
};
let caml_mutex_new  = (...args) => {
    // console.log('caml_mutex_new', args);
};

let gg = (n, f) => (...args) => {
    // console.log({n, args});
    if(!f)
	throw n;
    else
	return f(...args);
};

let that_is_my_wrapper = (...args) => {
    console.log(args);
}

let int128_init_custom_ops  = gg("int128_init_custom_ops ", _ => null);
let int128_max_int          = gg("int128_max_int         ", x => Math.pow(2,64));
let int128_min_int          = gg("int128_min_int         ", x => -Math.pow(2,64));
let int128_of_int           = gg("int128_of_int          ", n => n);
let int40_max_int           = gg("int40_max_int          ", x => Math.pow(2,64));
let int40_min_int           = gg("int40_min_int          ", x => -Math.pow(2,64));
let int40_of_int            = gg("int40_of_int           ", n => n);
let int48_max_int           = gg("int48_max_int          ", x => Math.pow(2,64));
let int48_min_int           = gg("int48_min_int          ", x => -Math.pow(2,64));
let int48_of_int            = gg("int48_of_int           ", n => n);
let int56_max_int           = gg("int56_max_int          ", x => Math.pow(2,64));
let int56_min_int           = gg("int56_min_int          ", x =>-Math.pow(2,64));
let int56_of_int            = gg("int56_of_int           ", n => n);
let uint128_init_custom_ops = gg("uint128_init_custom_ops", _ => null);
let uint128_max_int         = gg("uint128_max_int        ", x => Math.pow(2,64));
let uint128_of_int          = gg("uint128_of_int         ", x => x);
let uint32_init_custom_ops  = gg("uint32_init_custom_ops ", x => null);
let uint32_max_int          = gg("uint32_max_int         ", x => Math.pow(2,64));
let uint32_of_int           = gg("uint32_of_int          ", x => x);
let uint32_sub              = gg("uint32_sub             ", (x,y) => x-y);
let uint40_of_int           = gg("uint40_of_int          ", x => x);
let uint48_of_int           = gg("uint48_of_int          ", x => x);
let uint56_of_int           = gg("uint56_of_int          ", x => x);
let uint64_init_custom_ops  = gg("uint64_init_custom_ops ", x => null);
let uint64_max_int          = gg("uint64_max_int         ", x => Math.pow(2,64));
let uint64_of_int           = gg("uint64_of_int          ", x => x);
let uint64_sub              = gg("uint64_sub             ", (x,y) => x - y);
