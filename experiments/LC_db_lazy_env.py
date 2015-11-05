from LC_prog import *


def eval_(expr, env=None, debug=False):
    if not env:
        env = []
    return eval(to_de_bruijn(expr), env, debug=debug)


def to_thunk(v, env):
    if v[0] == Var:
        _var, x = v
        if x < len(env):
            return env[x]
        else:
            return None
    elif v[0] == Prim:
        return [True, v]
    else:
        return [False, [v, env]]


def eval(expr, env, case='eval', _state=None, debug=False):

    if not _state:
        _state = {'count': 0}

    def _eval(expr, env, case=''):
        typ = expr[0]
        _state['count'] += 1
        if typ == Var:
            _var, x = expr
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
            thunk_v = to_thunk(v, env)
            f_ = _eval(f, env, case='app-f')
            if f_[0] == Clo:
                _clo, body, env_ = f_
                return _eval(body, [thunk_v] + env_, case='app')
            elif f_[0] == Prim and f_[1] == Fun:
                _prim, _fun, prim_fun = f_
                v_ = _eval([Var, 0], [thunk_v] + env, case='prim-f')
                return prim_fun(v_)
            raise Exception(f_[0:2])
        else:
            return expr
    x = _eval(expr, env)
    if debug:
        print(_state)
    return x
