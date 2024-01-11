import sympy as sp

class Recurrence:
    def __init__(self, initial, branches):
        self._preprocess(initial, branches)

    def _preprocess(self, initial, branches):
        self.conditions = [branch[0] for branch in branches]
        self.transitions = [branch[1] for branch in branches]
        self.initial = initial

    def get_conditions(self):
        return self.conditions.copy()

    def get_transitions(self):
        return self.transitions.copy()
