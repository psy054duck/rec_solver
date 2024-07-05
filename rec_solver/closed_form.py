class ClosedForm:
    def __init__(self):
        pass

class PeriodicClosedForm(ClosedForm):
    def __init__(self, closed_form_list, ind_var):
        self._closed_form_list = closed_form_list
        self._ind_var = ind_var

    def eval_at(self, n):
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

    @property
    def period(self):
        return len(self._closed_form_list)

    @property
    def ind_var(self):
        return self._ind_var