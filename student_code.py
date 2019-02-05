import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []
    #Implement the `Retract` interface to remove facts from the KB
    #  - i.e., implement the `KnowledgeBase.kb_retract` method.
    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if isinstance(fact_or_rule, Fact):
            if fact_or_rule not in self.facts:
                #print("fact not in bk!")
                return
            else:
                #find the corresponding fact in kb
                index = self.facts.index(fact_or_rule)
                fact_or_rule = self.facts[index]
                #if the fact is not supported, remove it
                if len(fact_or_rule.supported_by) == 0:
                    self.facts.remove(fact_or_rule)
                else:
                    #print("can't retract!")
                    return
        elif isinstance(fact_or_rule, Rule):
            if fact_or_rule not in self.rules:
                #print("rule not in bk!")
                return
            else:
                #find the corresponding rule in kb
                index = self.rules.index(fact_or_rule)
                fact_or_rule = self.rules[index]
                #if rule is not supported and not asserted， then remove it
                if len(fact_or_rule.supported_by) == 0 and fact_or_rule.asserted != True:
                    self.rules.remove(fact_or_rule)
                else:
                    #print("can't retract!")
                    return
        #remove the supported pairs of the facts that it supports
        for facts in fact_or_rule.supports_facts:
            for i in facts.supported_by:
                if fact_or_rule in i:
                    facts.supported_by.remove(i)
            if facts.asserted != True:
                self.kb_retract(facts)
        #remove the supported pairs of the rules that it supports
        for rules in fact_or_rule.supports_rules:
            for i in rules.supported_by:
                if fact_or_rule in i:
                    rules.supported_by.remove(i)
            if rules.asserted != True:
                self.kb_retract(rules)


            
        


class InferenceEngine(object):
    #Implement the forward-chaining inferences that occurs upon asserting facts 
    # and rules into the KB - i.e., implement the `InferenceEnginer.fc_infer` method.
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        
        binds = match(fact.statement, rule.lhs[0])
        if binds != False:
            #if rule.lhs contains more than one item, a new rule should be inferred
            if len(rule.lhs) > 1:
                lhs = []
                rhs = Statement()
                for i in rule.lhs[1:]:
                    lhs.append(instantiate(i, binds))
                rhs = instantiate(rule.rhs, binds)
                newrule = Rule([lhs, rhs], [[fact, rule]])
                fact.supports_rules.append(newrule)
                rule.supports_rules.append(newrule)
                kb.kb_assert(newrule)
            else: 
                #there is only one item in rule.lhs, so new fact 
                newfact = Fact(instantiate(rule.rhs, binds), [[fact, rule]])
                fact.supports_facts.append(newfact)
                rule.supports_facts.append(newfact)
                kb.kb_assert(newfact)

        return



        
