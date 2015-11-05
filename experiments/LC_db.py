from LC_prog import *


def shift(expr, d, c=0):
    typ = expr[0]
    if typ == Var:
        _var, x = expr
        return [_var, x+d] if x >= c else expr
    elif typ == Lam:
        _lam, b = expr
        return [_lam, shift(b, d, c+1)]
    elif typ == App:
        _app, f, v = expr
        return [_app, shift(f, d, c), shift(v, d, c)]
    else:
        return expr


def subst(expr, name, val):
    typ = expr[0]
    if typ == Var:
        _var, x = expr
        if x == name:
            return shift(val, name)
        else:
            return [_var, x]
    elif typ == Lam:
        _lam, b = expr
        return [_lam, subst(b, name+1, val)]
    elif typ == App:
        _app, f, v = expr
        return [_app, subst(f, name, val), subst(v, name, val)]
    else:
        return expr


def eval(expr, weak=False, debug=False, _state=None):
    if not _state:
        _state = {'count': 0, 'subst': 0}

    def _eval(expr, weak=False):
        _state['count'] += 1
        typ = expr[0]
        if typ == Var:
            return expr
        elif typ == Lam:
            if weak:
                return expr
            else:
                _lam, b = expr
                return [_lam, _eval(b, weak)]
        elif typ == App:
            _app, f, v = expr
            f_ = _eval(f, weak=True)
            if f_[0] == Lam:
                _lam, b = f_
                _state['subst'] += 1
                return shift(_eval(subst(b, 0, shift(v, 1)), weak), -1)
            elif f_[0] == Prim and f_[1] == Fun:
                v_ = eval(v)
                return f_[2](v_)
            else:
                if weak:
                    return expr
                else:
                    return [_app, _eval(f), _eval(v)]
        else:
            return expr
    r = _eval(expr, weak=weak)
    if debug:
        print(_state)
    return r


def eval_(expr, debug=False):
    return eval(to_de_bruijn(expr), debug=debug)
