from LC_prog import *


def eval_(expr, env=None, global_env=None, pyenv=None, debug=False):
    if not env:
        env = []
    if not pyenv:
        pyenv = {}
    if not global_env:
        global_env = {}
    return eval(to_de_bruijn(expr, pyenv=pyenv),
                env, global_env=global_env, debug=debug, pyenv=pyenv)


def to_thunk(v, env, global_env):
    if v[0] == Var:
        _var, x = v
        if isinstance(x, int):
            if x < len(env):
                return env[x]
            else:
                return None
        else:
            if x in global_env:
                return global_env[x]
            else:
                return [False, [e, env]]
    elif v[0] == Prim:
        return [True, v]
    else:
        return [False, [v, env]]


def eval(expr, env, global_env=None,
         case='eval', _state=None, debug=False, pyenv=None):

    if not _state:
        _state = {'count': 0}
    if not pyenv:
        pyenv = {}

    def _eval(expr, env, case=''):
        typ = expr[0]
        _state['count'] += 1
        if typ == Var:
            _var, x = expr
            env = env if isinstance(x, int) else global_env
            computed, v = env[x]
            if not computed:
                expr_, env_ = v
                env[x][0] = True
                env[x][1] = _eval(expr_, env_, case='var')
            return env[x][1]
        elif typ == Lam:
            _lam, body = expr
            return [Clo, body, env]
        elif typ == App:
            _app, f, v = expr
            thunk_v = to_thunk(v, env, global_env)
            f_ = _eval(f, env, case='app-f')
            if f_[0] == Clo:
                _clo, body, env_ = f_
                return _eval(body, [thunk_v] + env_, case='app')
            elif f_[0] == Prim and f_[1] == Fun:
                _prim, _fun, prim_fun, n, args = f_
                v_ = _eval([Var, 0], [thunk_v] + env, case='prim-f')
                args = args + [v_]
                if n == 1:
                    res = to_de_bruijn(prim_fun(*args), pyenv=pyenv)
                    return _eval([Var, 0], [to_thunk(res, env, global_env)])
                else:
                    return [_prim, _fun, prim_fun, n-1, args]
            raise Exception(f_[0:2])
        else:
            return expr
    x = _eval(expr, env)
    if debug:
        print(_state)
    return x


def loads(fp):
    from json import load
    return load(fp)

if __name__ == '__main__':
    from optparse import OptionParser
    from sys import stdin
    usage = 'usage: %prog [options]'
    parser = OptionParser(usage=usage)
    parser.add_option('-f', '--file',
                      dest='filename', action='store', type='string')
    parser.add_option('-m', '--modules',
                      dest='modules', action='store',
                      type='string', default='')
    options, args = parser.parse_args()
    if options.filename:
        file = open(options.filename)
    elif len(args) > 0:
        file = open(args[0])
    else:
        file = stdin
    modules = options.modules.split()
    env = {}
    exec('\n'.join(['import {}'.format(m) for m in modules]), env)
    loaded = loads(file)
    global_env = {}
    for n, f in bindings:
        global_env[n] = to_thunk(to_de_bruijn(f), [], global_env)
    eval_(loaded, pyenv=env, global_env=global_env)
