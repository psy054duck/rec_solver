import sympy as sp

class ClosedForm:
    def __init__(self):
        pass

class PeriodicClosedForm(ClosedForm):
    def __init__(self, closed_form_list, ind_var):
        self._closed_form_list = closed_form_list
        self._ind_var = ind_var

    def eval_at(self, n):
        assert(n >= 0)
        r = n % self.period
        val = {k: c.subs(self.ind_var, n) for k, c in self._closed_form_list[r]}
        return val

    def subs(self, mapping):
        new_list = []
        for part in self._closed_form_list:
            cur_closed = {k: c.subs(mapping, simultaneous=True) for k, c in part.items()}
            new_list.append(cur_closed)
        return PeriodicClosedForm(new_list, self.ind_var)

    def __str__(self):
        return str(self._closed_form_list)

    def get_rth_part_closed_form(self, r):
        return self._closed_form_list[r]

    @property
    def period(self):
        return len(self._closed_form_list)

    @property
    def ind_var(self):
        return self._ind_var

class PiecewiseClosedForm(ClosedForm):
    def __init__(self, thresholds=[], closed_forms=[], ind_var=sp.Symbol('n', integer=True)):
        if sp.oo in thresholds:
            std_thresholds = thresholds
        else:
            std_thresholds = thresholds + [sp.oo]
        self._closed_forms = closed_forms
        self._ind_var = ind_var
        self._intervals = self._compute_intervals(std_thresholds)

    def concatenate(self, latter_closed):
        new_thresholds = self.thresholds + latter_closed.thresholds
        new_closed_forms = self.closed_forms + latter_closed.closed_forms
        return PiecewiseClosedForm(new_thresholds, new_closed_forms, self.ind_var)


    def eval_at(self, n):
        assert(n >= 0)
        is_larger = [n > t for t in self.thresholds]
        which = is_larger.index(False) - 1
        return self.closed_forms[which].subs({self.ind_var: n})

    def subs(self, mapping):
        intervals = self._intervals_after_mapping_n(mapping)
        thresholds = [interval.left for interval in intervals]
        closed_forms = [c.subs(mapping) for c in self.closed_forms]
        return PiecewiseClosedForm(thresholds, closed_forms, self.ind_var)

    def _intervals_after_mapping_n(self, mapping):
        new_intervals = []
        for interval in self.intervals:
            rel = interval.as_relational(self.ind_var).subs(mapping, simultaneous=True)
            new_intervals.append(rel.as_set())
        return new_intervals

    def __str__(self):
        res = ''
        str_intervals = [str(interval.as_relational(self.ind_var)) for interval in self.intervals]
        max_prefix_len = max([len(s) for s in str_intervals])
        for interval, closed in zip(str_intervals, self.closed_forms):
            res += '{0:{width}}: '.format(interval, width=max_prefix_len)
            res += str(closed) + '\n'
        return res


    def _compute_intervals(self, thresholds):
        res = []
        for i in range(len(thresholds) - 1):
            left = thresholds[i]
            right = thresholds[i + 1]
            res.append(sp.Interval(left, right, left_open=False, right_open=True))
        return res

    @property
    def closed_forms(self):
        return self._closed_forms

    @property
    def ind_var(self):
        return self._ind_var

    @property
    def intervals(self):
        return self._intervals

    @property
    def thresholds(self):
        return [interval.left for interval in self.intervals]