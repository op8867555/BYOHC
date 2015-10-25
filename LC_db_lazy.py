from LC_prog import *


Trace = 'trace'


def shift(expr, d, c=0):
    if not expr:
        return None
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


def eval0(expr, weak=False, _state=None, debug=False):
    if not _state:
        _state = {'count': 0, 'subst': 0}

    def eval(expr, weak=False):
        _state['count'] += 1
        typ = expr[0][0]
        if typ == Var:
            pass
        elif typ == Lam:
            if not weak:
                _lam, b = expr[0]
                expr[0][1] = eval(b, weak)
        elif typ == App:
            _app, f, v = expr[0]
            f_ = eval(f, weak=True)
            expr[0][1] = f_
            if f_[0][0] == Lam:
                _lam, b = f_[0]
                _state['subst'] += 1
                sub = subst(unbox(b), 0, shift(unbox(v), 1))
                evaluated = unbox(eval(box(sub), weak))
                shifted = shift(evaluated, -1)
                if debug:
                    print('substitute 0 with: {}'.format(sub))
                    print('evaluated: {}'.format(evaluated))
                    print('shifted: {}'.format(shifted))
                expr[0] = box(shifted)[0]
            elif f_[0][0] == Prim and f_[0][1] == Fun:
                v_ = eval(v)
                _prim, _fun, f = f_[0]
                expr[0] = f(unbox(v_))
            else:
                if not weak:
                    expr[0][1] = eval(f)
                    expr[0][2] = eval(v)
        return expr
    expr = eval(expr)
    if debug:
        print(_state)
        return expr
    else:
        return expr


def box(expr):
    typ = expr[0]
    if typ == Var:
        return [expr]
    elif typ == App:
        app_, f, v = expr
        return [[App, box(f), box(v)]]
    elif typ == Lam:
        _lam, x = expr
        return [[Lam, box(x)]]
    elif typ == Prim:
        return [expr]
    else:
        raise Exception(expr)


def unbox(expr):
    typ = expr[0][0]
    if typ == Var:
        return expr[0]
    elif typ == App:
        _app, f, v = expr[0]
        return [App, unbox(f), unbox(v)]
    elif typ == Lam:
        _lam, x = expr[0]
        return [Lam, unbox(x)]
    elif typ == Prim:
        return expr[0]
    else:
        raise Exception(str(expr))


def eval_(expr, debug=False, weak=False):
    return unbox(eval0(box(to_de_bruijn(expr)), debug=debug, weak=weak))
