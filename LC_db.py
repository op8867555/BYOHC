from LC_common import Var, Lam, App, to_de_bruijn


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


count = [0]


def _eval(expr, weak=False):
    count[0] += 1
    return eval(expr, weak)


def eval(expr, weak=False):
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
            return shift(_eval(subst(b, 0, shift(v, 1)), weak), -1)
        else:
            if weak:
                return expr
            else:
                return [_app, _eval(f), _eval(v)]


def eval_(expr):
    return _eval(to_de_bruijn(expr))

'''

def eval_env(expr, stack=None, weak=False, debug=False, case='eval'):
    def abs(stack):
        return ['Unbound'] + stack

    if not stack:
        stack = []

    if debug:
        print(case)
        print(expr)
        print(stack)

    typ = expr[0]
    if typ == Var:
        _var, x = expr
        try:
            v = stack[x]
            if v == 'Unbound':
                return expr
            else:
                return shift(v, x)
        except Exception:
            # print('ERROR')
            # print(expr)
            # print(stack)
            return shift(expr, x)

    elif typ == Lam:
        if weak:
            return expr
        else:
            _lam, b = expr
            return [Lam, eval_env(b, abs(stack), debug=debug, case='lam')]
    elif typ == App:
        _app, f, v = expr
        f_ = eval_env(f, stack, weak=True, debug=debug, case='app0')
        if f_[0] == Lam:
            _lam, b = f_
            return eval_env(b, [v] + stack[1:], weak, debug=debug, case='app')
        else:
            if weak:
                return expr
            else:
                return [_app,
                        eval_env(f, stack, debug=debug, case='app_f'),
                        eval_env(v, stack, debug=debug, case='app_v')]

'''
