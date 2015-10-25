Var = 'var'
Lam = 'lam'
App = 'app'

Clo = 'clo'
Prim = 'prim'
Int = 'int'
Fun = 'fun'
Bool = 'bool'
List = 'list'


def app(f, *vs):
    try:
        f[0]
        ans, *vs = vs
        ans = [App, f, ans]
        for v in vs:
            ans = [App, ans, v]
        return ans
    except ValueError as e:
        raise e


def lam(xs, b):
    if not isinstance(xs, list):
        return [Lam, xs, b]
    ans, *xs = reversed(xs)
    ans = [Lam, ans, b]
    for x in xs:
        ans = [Lam, x, ans]
    return ans


def var(x):
    return [Var, x]


def to_de_bruijn(expr, stack=None):
    if not stack:
        stack = []
    if isinstance(expr, str):
        expr = [Var, expr]
    try:
        typ, x = expr[0:2]
    except ValueError:
        raise Exception('to_de_bruijn: ' + repr(expr))
    if typ == Lam:
        body = expr[2]
        return [Lam, to_de_bruijn(body, [x] + stack)]
    elif typ == Var:
        idx = stack.index(x)
        return [Var, idx]
    elif typ == App:
        y = expr[2]
        return [App, to_de_bruijn(x, stack), to_de_bruijn(y, stack)]
    else:
        return expr


def scott_to_int(x):
    z = to_de_bruijn(c0)
    if x == z:
        return 0
    else:
        [_l, [_l, [_app, _s, n]]] = x
        return scott_to_int(n) + 1


def scott_to_list(xs, f=None):
    n = to_de_bruijn(nil)
    if xs == n:
        return []
    else:
        [_l, [_l, [_a, [_a, _c, x], xs]]] = xs
        if f:
            x = f(x)
        return [x] + scott_to_list(xs, f)


def nat(x):
    n = lam(['s', 'n'], [Var, 'n'])
    for i in range(x):
        n = lam(['s', 'n'], app(var('s'), n))
    return n


bottom = None

Y = lam('f', app(lam('x', app(var('f'), app(var('x'), var('x')))),
                 lam('x', app(var('f'), app(var('x'), var('x'))))))
bottom = app(Y, Y)

c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 = map(nat, range(10))

true = lam('t', lam('f', var('t')))
false = lam('t', lam('f', var('f')))

const = lam('a', lam('b', var('a')))
succ = lam('n', lam('s', lam('z', app(var('s'), var('n')))))
pred = lam('n', app(app(var('n'), lam('n-', var('n-'))), c0))


add_ = lam('+', lam('a', lam('b',
           app(app(var('a'), lam('a-',
                   app(app(var('+'), var('a-')), app(succ, var('b'))))),
               var('b')))))

add = app(Y, add_)

'''
const a b = a
eq m n = m (\m-. n (\n-. eq m- n-)) false) (n (const false) true)
'''
eq_ = lam('eq_', lam('m', lam('n',
          app(app(var('m'),
              lam('m-', app(app(var('n'), lam('n-',
                  app(app(var('eq_'), var('m-')), var('n-')))),
                  false))),
              app(app(var('n'), app(const, false)), true)))
          ))

eq = app(Y, eq_)

cons = lam(['h', 't', 'cons', 'nil'], app('cons', 'h', 't'))

nil = lam(['cons', 'nil'], 'nil')

pair = lam(['a', 'b', 'p'], app('p', 'a', 'b'))

'''
take n xs = n (\ n- -> xs (\ x xs -> (:) x (take n- xs)) nil)
              (xs (\ x xs -> (:) x []) bottom)

take _ [] = []
take 0 (x:xs) = [x]
take n (x:xs) = x : take (n-1) xs
'''
take_ = lam(['take', 'n', 'xs'],
            app('n',
                lam('n-',
                    app('xs',
                        lam(['x', 'xs'],
                            app('cons', 'x', app('take', 'n-', 'xs'))),
                        'nil')),
                app('xs',
                    lam(['x', 'xs'], app('cons', 'x', 'nil')),
                    'bottom')))

take = app(Y, take_)


'''
tail xs = xs (\ x xs -> xs) bottom
'''
tail = lam('xs', app(lam(['x', 'xs'], 'xs'), 'bottom'))

'''
zipWith = Y $ \ zip_ f a b ->
    a (\ x xs -> b (\ y ys -> cons (f x y) (zip_ xs ys)) nil ) nil
'''


zipWith_ = lam(['zipWith_', 'f', 'a', 'b'],
               app('a',
                   lam(['x', 'xs'],
                       app('b',
                           lam(['y', 'ys'],
                               app('cons',
                                   app('f', 'x', 'y'),
                                   app('zipWith_', 'xs', 'ys'))),
                           'nil')),
                   'nil'))

zipWith = app('Y', zipWith_)

'''
fibs = 1 : 1 : zipWith (+) fibs (tail fibs)
'''

fibs_ = lam('fibs',
            app('cons',
                '1',
                app('cons',
                    '1',
                    app('zipWith', '+', 'fibs', app('tail', 'fibs')))))

fibs__ = lam('fibs_', app(app('cons', '1'),
             app(app(cons, '1'), app(app(app(zipWith, '+'), var('fibs_')),
                 app(tail, var('fibs_'))))))


fibs = app(Y, fibs_)


def fun(expr):
    return [Prim, Fun, expr]


def scott_list(xs, f=None):
    ys = nil
    for x in reversed(xs):
        if f:
            x = f(x)
        ys = app(app(cons, x), ys)
    return ys


def define(xs):
    def ret(x):
        res = x
        for (name, fun) in reversed(xs):
            res = app(lam(name, res), fun)
        return res
    return ret


def succ_int(expr):
    _prim, _int, x = expr
    return [_prim, Int, x+1]


def add_int(a):
    def add_a(b):
        _prim, _int, m = a
        _prim, _int, n = b
        return [_prim, _int, m + n]
    return [Prim, Fun, add_a]


def if_prim(expr):
    def if1(a):
        def if2(b):
            _prim, _bool, x = expr
            return a if x else b
        return fun(if2)
    return fun(if1)


'''
to_int = λx x ( λx- succ(to_int x-)) 0 '
'''


def prelude(prog):
    to_int_ = lam(['to_int', 'x'],
                  app(var('x'),
                      lam('x-', app(var('succ'),
                                    app(var('to_int'), var('x-')))),
                      var('0')))

    to_list_ = lam(['to_list_', 'xs'],
                   app('xs',
                       lam(['x', 'xs'],
                           app(':', 'x', app('to_list_', 'xs'))),
                       '[]'))

    def p(x):
        print(x)
        return x

    def cons_prim(x):
        def cons_x(xs):
            _prim, _list, xs = xs
            return [_prim, _list, [x]+xs]
        return [Prim, Fun, cons_x]

    fs = [('Y', Y),
          ('bottom', bottom),
          ('0', [Prim, Int, 0]),
          ('1', [Prim, Int, 1]),
          ('succ', [Prim, Fun, succ_int]),
          ('+', [Prim, Fun, add_int]),
          ('if', [Prim, Fun, if_prim]),
          ('to_int', app('Y', to_int_)),
          ('print', [Prim, Fun, p]),
          ('[]', [Prim, List, []]),
          (':', [Prim, Fun, cons_prim]),
          ('to_list', app('Y', to_list_)),
          ('cons', cons),
          ('nil', nil),
          ('tail', tail),
          ('take', take),
          ('zipWith', zipWith)
          ]
    return define(fs)(prog)
