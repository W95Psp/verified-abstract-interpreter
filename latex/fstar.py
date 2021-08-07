from pygments.lexer import RegexLexer, bygroups, inherit
from pygments.lexers.ml import FStarLexer
from pygments.token import *
from pygments.filter import Filter, simplefilter
from pygments.filters import KeywordCaseFilter
from pygments.util import get_bool_opt
import sys
import re


def replace_text_veffect(text):
    text = re.sub(r"hVal (int|ℤ)", r"!\\ensuremath{\\mathbb{Z}_h}!", text)
    text = re.sub(r"hVal unit", r"unit!\\ensuremath{{}_h}!", text)
    text = re.sub(r"ST_h", r"ST!\\ensuremath{{}_{\\PYG{nc}{\\ensuremath{h}}}}!", text)
    text = re.sub(r"^(.)Val$", r"!\\ensuremath{\\textrm{\\textsc{val}}_{\1}}!", text)
    text = re.sub(r"^([a-z][a-zA-Z]*)_(r)$", r"\1!\\ensuremath{{}_{\2}}!", text)
    text = re.sub(r"\b([a-z]|monotony|body)_([wW])\b", r"\1!\\ensuremath{{}_{\\ImpMonadLetter{}}}!", text)
    return text

def process_veffect(value):
    return value

def process_veffect_contexts(value):
    test0 = re.search(r"^(.)([A-Z])([0-9nNM]?)('?)$", value)
    if test0 and value != "ST":
        num = test0.group(3)
        l = test0.group(1)
        yep = not (l == "a" or l == "w")
        l = "{\\texttt{\\hashsymbol}}" if l=="a" else l
        l = "\\ImpMonadLetter{}" if l=="w" else l
        num = "{n+1}" if num=="N" else num
        num = "{n-1}" if num=="M" else num
        num = "{n+2}" if num=="O" else num
        suffix = "^{"+l+"}_"+num
        if num == "":
            suffix = "_{"+l+"}"
        suffix += test0.group(4)
        value = test0.group(2).lower() + '!\\ensuremath{{}' + suffix + '}!'
    else:
        value = re.sub(r"^([a-z][a-zA-Z]*)(\d+)$", r"\1!\\ensuremath{{}_{\2}}!", value)
    test = re.search(r"^(`?)([^`])_([a-zA-Z_']+)_`?$", value)
    if test:
        w = test.group(2)
        wo = test.group(2)
        if w=="w":
            w = "\\ImpMonadLetter{}"
        if w=="a":
            w = "{\\texttt{\\hashsymbol}}"
        def h(n, more=''):
            return '!\ensuremath{'+n+'_'+w+more+'}!'
        def g(n, more=''):
            return n+'!\ensuremath{{}_'+w+more+'}!'
        def f(op):
            wd = w
            if op == ";":
                wd = "{\scalebox{0.5}{"+w+"}}";
            if test.group(1) == "`":
                return '!\ensuremath{{'+op+'}_'+wd+'}!'
            else:
                return '(!\ensuremath{{'+op+'}_'+wd+'}!)'
        value = {
            'gamma': "!\\ensuremath{\\gamma}!", 'gamma_st_w': "!\\ensuremath{\\gamma_{\\textsc{st}}}!",
            'gamma_val_w': "!\\ensuremath{\\gamma_{\\textsc{val}}}!", 'aState_eq': '=',
            'assume': g('ass!{}!ume'), 'widen': '!\\ensuremath{\\nabla}\,!',
            'iWP': g('iSP' if wo=='a' else 'iWP'), 'eWP': g('eSP' if wo=='a' else 'eWP'),
            'pre': g('pre'), 'post': g('post'), 'po': g('!{\\textrm{PO}}!'),
            'wp\'': g('wp'), 'wp': g('wp'), 'const': g('const'),
            'post_lift\'': g('post', '^{\\uparrow}'), 'wp_lift\'': g('wp', '^{\\uparrow}'),
            'post_lift': g('post', '^{\\downarrow}'), 'wp_lift': g('wp', '^{\\downarrow}'),
            'return': g('return'), 'addition': f('+'), 'subtraction': f('-'),
            'bind': f('{\\bindSymbol{}}'), 'if': g('i!{}!f'), 'while': g('while'),
            'not': h('\\texttt{\\bang}'), 'eq': f('='), 'lt': f('>'), 'and': f('&&'),
            'var': g('var'), 'alloc': g('alloc'), 'store': g('store'), 'sequence': f(';'),
        }.get(test.group(3), value)
        print("value=" + value)
    return value



def replace_effect_operators(text):
    par = lambda s: "(" + s + ")"
    identity = lambda x: x 
    effectOperators = {
        "return": lambda eff, _: "ret!\\ensuremath{{}_{" + eff + "}}!",
        "bind": lambda eff, infix: (identity if infix else par)("!\\ensuremath{\\bindSymbol{}_{" + eff + "}}!")
    }
    cb = lambda infix: lambda x: effectOperators.get(x[1], lambda _,__: x[0])(x[2], infix)
    text = re.sub(r"`_(\w+)_(\w+)_`", cb(True), text)
    text = re.sub(r"\b_(\w+)_(\w+)_\b", cb(False), text)
    return text


def replace_text_ab_int(text):
    text = re.sub(r"\bint_m\b", r"i!{}!nt_m", text);
    text = re.sub(r"\bbackward_lt_true\b", r"!$\\overleftarrow{\\texttt{lt}}_{\\texttt{true}}$!", text)
    text = re.sub(r"\bbackward_([a-z]+)ⵌ\b", r"!$\\overleftarrow{\\texttt{\1}^\\#}$!", text)
    text = re.sub(r"\bbackward_([a-z]+)\b", r"!$\\overleftarrow{\\texttt{\1}}$!", text)
    text = re.sub(r"\bbackward_abstract_binop'_lemma", r"backw!{}!ard_abstract_binop'_lemma", text)
    text = re.sub(r"\bbackward_(abstract_binop')(?!_)", r"!$\\overleftarrow{\\texttt{abstract\\_binop'}}$!", text)
    text = re.sub(r"\bbackward_(abstract_binop)(?!_)", r"!$\\overleftarrow{\\texttt{abstract\\_binop}}$!", text)
    text = re.sub(r"\bbackward_(asem_fp)(?!_)", r"!$\\overleftarrow{\\texttt{asem}}$!_fp", text)
    text = re.sub(r"\b([a-z])ⵌ([0-9])\b", r"\1!\\oneCharSubLD{\2}!", text)
    text = re.sub(r"\b([a-z]+)ⵌ_([a-z]{3})\b", r"\1!\\twoCharSubLD{\2}!", text)
    text = re.sub(r"\b([a-z]+)ⵌ_(?!norm)([a-z]{4})\b", r"\1!\\threeCharSubD{\2}!", text)
    text = re.sub(r"\b([a-z]+)ⵌ_([a-z])\b", r"\1!\\oneCharSubD{\2}!", text)
    text = re.sub(r"\b([a-z]+)ⵌ_([a-z]{2})\b", r"\1!\\twoCharSubLD{\2}!", text)
    text = re.sub(r"\b([a-z]+)_([a-z]{3})\b", r"\1!\\twoCharSubL{\2}!", text)
    text = re.sub(r"\b([a-z]+)_(?!norm)([a-z]{4})\b", r"\1!\\threeCharSub{\2}!", text)
    text = re.sub(r"\b([a-z]+)_([a-zA-Z])\b", r"\1!\\oneCharSub{\2}!", text)
    text = re.sub(r"\b([a-z]+)_([a-z]{2})\b", r"\1!\\twoCharSubL{\2}!", text)
    text = re.sub(r"\b([a-z]+)_gamma\b", r"\1!\\oneCharSubL{γ}!", text)
    text = re.sub(r"\b([a-z]+)_cgamma\b", r"\1!\\twoCharSubL{cγ}!", text)
    return text

symbols_veffect = { "hState": "!\\ensuremath{\\mathbb{M}_{h}}!",
                    "wState": "!\\ensuremath{\\mathbb{M}}!",
                    "aState": "!\\ensuremath{\\mathbb{M}^{\\texttt{\\hashsymbol}}}!",
                    "StuckState": "!\\ensuremath{\\bot^{\\texttt{\\hashsymbol}}_\mathbb{M}}!",
                    "varName": "!\\ensuremath{\\mathbb{V}}!",
                    "ALPHA": "!\\ensuremath{\\alpha}!",
                    "representation": "TypeR",
                    "val_repr": "va!{}!l!\\ensuremath{{}_{repr}}!",
                    "comp_repr": "comp!\\ensuremath{{}_{repr}}!",
                    "aSI": "s!\\ensuremath{{}_{\\alpha}^i}!",
                    "aSI'": "s!\\ensuremath{{}_{\\alpha}^{i'}}!",
                    "abTopMem": "!\\ensuremath{\\top^{\\texttt{\\hashsymbol}}_\\mathbb{M}}!",
                    "abTop": "!\\ensuremath{\\top^{\\texttt{\\hashsymbol}}}!",
                    "int_32": "!\\ensuremath{\\texttt{int}_{32}}!",
                    "aInt": "!\\ensuremath{\\mathbb{Z}^{\\texttt{\\hashsymbol}}}!",
                    "ST_h": "ST!\\ensuremath{{}_h}!",
                    "_APPROXTYPE_": "!\\ensuremath{\alpha T}!" }

symbols_g = {"->" : "→", "gamma": "γ", "'"  : "" , "<>" : "≠", "*"   : "×",
             "<-" : "!\\ensuremath{\\leftarrow}!"   , "int": "ℤ", "True": "⊤",
             "False": "⊥", "fun": "λ", "\\/": "∨", "/\\": "∧", "exists": "∃",
             "forall":"∀", "nat": "ℕ","beta": "β", "<=":"≤",">=":"≥","+^": "+" }

symbols_abint = {
    "max_int_m": "max!\\ensuremath{{}_{\\texttt{int}_\\texttt{m}}}!",
    "min_int_m": "min!\\ensuremath{{}_{\\texttt{int}_\\texttt{m}}}!",
    "size_int_m": "size!\\ensuremath{{}_{\\texttt{int}_\\texttt{m}}}!",
    "sound_backward_op": "sound!\\ensuremath{{}_{\\overleftarrow{op}}}!"
}

symbols = {**symbols_g, **symbols_veffect, **symbols_abint}

class CustomLexer(FStarLexer):

    tokens = {
        'root': [
            (r'\/\/.+$', Comment),
            inherit
        ]
    }
    
    def get_tokens_unprocessed(self, text):
        last = None
        llast = None
        
        text = re.sub(r'\(\*([\u2460-\u24FF])\*\)', r"\1", text)
        
        text = re.sub(r"\bint(?!_)\b", r"ℤ", text);
        text = re.sub(r"\(\|", r"⦇", text);
        text = re.sub(r"\|\)", r"⦈", text);
        text = re.sub(r"<==>", r"⇔", text)
        text = re.sub(r"==>", r"⇒", text)
        
        text = replace_effect_operators(text)
        text = replace_text_veffect(text)
        text = replace_text_ab_int(text)

        text = re.sub(r"'([a-z])([0-9]|n|n+1|n-1|i)\b", r"'\1!\\ensuremath{{}_{\2}}!", text)
        text = re.sub(r"\b([a-z]|monotony)_([a-z]|W)\b", r"\1!\\ensuremath{{}_{\2}}!", text)
    
        text = re.sub(r"([a-z])([0-9]+)\b", lambda x: x[1]+''.join(["₀₁₂₃₄₅₆₇₈₉"[int(x)] for x in x[2]]), text)
        
        for index, token, value in RegexLexer.get_tokens_unprocessed(self, text):
            if token == Token.Error:
                token = Token.Other
            value = process_veffect(value)
            # value = process_veffect_contexts(value)
            
            if last == "'" and len(value)==1:
                value = { k: "!\\ensuremath{\\" + v + "}!"
                    for k, v in
                    { 'a': 'tau', 'b': 'beta', 'c': 'gamma', 'd': 'delta', 'e': 'epsilon', 'f': 'phi',
                      'h': 'eta', 'i': 'iota', 'k': 'kappa', 'l': 'lambda', 'm': 'mu', 'n': 'nu',
                      'p': 'pi', 's': 'sigma', 't': 'tau' }.items()
                }.get(value, "'"+value)
            if value == "assert" or value == "class" or value == "instance":
                yield index, Token.Keyword, value
            elif value == "'":
                yield index, token, ""
            elif last == "fun" and value == " ":
                yield index, token, "!{}!"
            elif value in symbols:
                yield index, token, symbols[value]
            else:
                yield index, token, value
            llast = last
            last = value
                
