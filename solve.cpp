#include <bits/stdc++.h>

using namespace std;

typedef uint8_t vertex_t;
typedef pair<vertex_t, vertex_t> edge_t;

typedef uint32_t state_t;
typedef vertex_t event_t;

struct WalkableDFA {
	WalkableDFA() {}
	virtual ~WalkableDFA() {};

	virtual void reset() = 0;
	virtual state_t current_state() const = 0;
	virtual vector<event_t> event_options() const = 0;
	virtual void push_event(event_t event) = 0;
	virtual void pop() = 0;
	virtual bool is_accepting() const = 0;

	//private
	bool dfs(vector<event_t> &solution, unordered_set<state_t> &visited) {
		state_t curr  = current_state();
		if (visited.count(curr)) return false;
		visited.insert(curr);

		if (is_accepting()) return true;

		for (event_t event : event_options()) {
			push_event(event);
			solution.push_back(event);
			if (dfs(solution, visited)) return true;
			solution.pop_back();
			pop();
		}

		return false;
	}

	optional<vector<event_t>> find_solution() {
		vector<event_t> result;
		unordered_set<state_t> visited;
		return dfs(result, visited) ? optional<vector<event_t>>(result) : nullopt;
	}
};

struct DFA {
	vector<map<event_t, state_t>> transitions;
	unordered_set<state_t> accepting;

	state_t add_state(bool accept = false) {
		state_t result = transitions.size();
		transitions.emplace_back();
		if (accept) accepting.insert(result);
		return result;
	}

	void add_transition(state_t from, event_t event, state_t to) {
		transitions[from][event] = to;
	}

	//private
	state_t dfs_walkable(WalkableDFA &walkable, unordered_map<state_t, state_t> &reindex) {
		state_t curr = walkable.current_state();

		if (reindex.count(curr)) return reindex[curr];
		state_t from = add_state(walkable.is_accepting());
		reindex.emplace(curr, from);

		for (event_t event : walkable.event_options()) {
			walkable.push_event(event);
			add_transition(from, event, dfs_walkable(walkable, reindex));
			walkable.pop();
		}

		return from;
	}

	DFA(WalkableDFA &walkable) {
		walkable.reset();
		unordered_map<state_t, state_t> reindex;
		dfs_walkable(walkable, reindex);
	}

	DFA() {};

	size_t num_states() {
		return transitions.size();
	}

	size_t num_transitions() {
		return accumulate(transitions.begin(), transitions.end(), 0, [](size_t lhs, auto rhs){ return lhs + rhs.size(); });
	}
};

struct AtomicDFA : WalkableDFA {
	DFA dfa;
	stack<state_t> s;

	void reset() {
		s = stack<state_t>();
		s.push(0);
	}

	AtomicDFA(DFA dfa) : dfa(dfa) { reset(); }

	state_t current_state() const { return s.top(); }

	vector<event_t> event_options() const {
		vector<event_t> result;
		const auto &m = dfa.transitions[current_state()];
		result.reserve(m.size());
		transform(m.begin(), m.end(), inserter(result, result.end()), [](auto p){ return p.first; });
		return result;
	}

	void push_event(event_t event) {
		s.push(dfa.transitions[current_state()][event]);
	}

	void pop() {
		if (s.size() > 1) s.pop();
	}

	bool is_accepting() const {
		return dfa.accepting.count(current_state());
	}
};

struct pair_hash {
	template <class T1, class T2>
	size_t operator() (const pair<T1, T2> &p) const { return hash<T1>()(p.first) ^ hash<T2>()(p.second); }
};

struct ConjunctionDFA : WalkableDFA {
	WalkableDFA *lhs, *rhs;
	stack<state_t> s;
	unordered_map<pair<state_t, state_t>, state_t, pair_hash> compress;

	//private
	state_t add_state(state_t l, state_t r) {
		auto p = make_pair(l, r);

		if (!compress.count(p)) compress.emplace(p, compress.size());

		return compress[p];
	}

	void reset() {
		lhs->reset();
		rhs->reset();
		s = stack<state_t>();
		compress.clear();
		
		state_t curr = add_state(lhs->current_state(), rhs->current_state());
		s.push(curr);
	}

	ConjunctionDFA(WalkableDFA *lhs, WalkableDFA *rhs) : lhs(lhs), rhs(rhs) {
		assert(lhs != nullptr);
		assert(rhs != nullptr);
		reset();
	}

	~ConjunctionDFA() {
		delete lhs;
		delete rhs;
	}

	state_t current_state() const { return s.top(); }

	vector<event_t> event_options() const {
		auto lv = lhs->event_options();
		auto rv = rhs->event_options();
		vector<event_t> result;
		result.reserve(min(lv.size(), rv.size()));
		set_intersection(lv.begin(), lv.end(), rv.begin(), rv.end(), inserter(result, result.end()));
		return result;
	}

	void push_event(event_t event) {
		lhs->push_event(event);
		rhs->push_event(event);
		state_t curr = add_state(lhs->current_state(), rhs->current_state());
		s.push(curr);
	}

	void pop() {
		if (s.size() > 1) {
			lhs->pop();
			rhs->pop();
			s.pop();
		}
	}

	bool is_accepting() const {
		return lhs->is_accepting() && rhs->is_accepting();
	}
};

WalkableDFA *dfa_conjunction(vector<WalkableDFA*> &dfas, int lwr = 0, int upr = -1) {
	if (upr == -1) upr = dfas.size();
	if (upr - lwr < 2) return dfas[lwr];
	int mid = (lwr + upr) / 2;
	return new ConjunctionDFA(dfa_conjunction(dfas, lwr, mid), dfa_conjunction(dfas, mid, upr));
}

DFA edge_to_dfa_parity(vertex_t u, vertex_t v, const vector<vertex_t> &vs) {
	DFA result;
	state_t init = result.add_state();		for (vertex_t v : vs) result.add_transition(init, v, init);
	state_t su = result.add_state();		for (vertex_t v : vs) result.add_transition(su, v, su);
	state_t suv = result.add_state();		for (vertex_t v : vs) result.add_transition(suv, v, suv);
	state_t suvu = result.add_state(true);	for (vertex_t v : vs) result.add_transition(suvu, v, suvu);
	result.add_transition(init, u, su);
	result.add_transition(su, v, suv);
	result.add_transition(suv, u, suvu);
	return result;
}

DFA edge_to_dfa(vertex_t u, vertex_t v, const vector<vertex_t> &vs) {
	DFA lhs = edge_to_dfa_parity(u, v, vs);
	DFA rhs = edge_to_dfa_parity(v, u, vs);
	WalkableDFA *walkable = new ConjunctionDFA(new AtomicDFA(lhs), new AtomicDFA(rhs));
	DFA result(*walkable);
	delete walkable;
	return result;
}

DFA exclude_edge_to_dfa_parity(vertex_t u, vertex_t v, const vector<vertex_t> &vs) {
	DFA result;
	state_t init = result.add_state(true);		for (vertex_t v : vs) result.add_transition(init, v, init);
	state_t su = result.add_state(true);		for (vertex_t v : vs) result.add_transition(su, v, su);
	state_t suv = result.add_state(true);		for (vertex_t v : vs) result.add_transition(suv, v, suv);
	state_t suvu = result.add_state(true);		for (vertex_t v : vs) result.add_transition(suvu, v, suvu);
	state_t suvuv = result.add_state();
	result.add_transition(init, u, su);
	result.add_transition(su, v, suv);
	result.add_transition(suv, u, suvu);
	result.add_transition(suvu, v, suvuv);
	return result;
}

DFA exclude_edge_to_dfa(vertex_t u, vertex_t v, const vector<vertex_t> &vs) {
	DFA lhs = exclude_edge_to_dfa_parity(u, v, vs);
	DFA rhs = exclude_edge_to_dfa_parity(v, u, vs);
	WalkableDFA *walkable = new ConjunctionDFA(new AtomicDFA(lhs), new AtomicDFA(rhs));
	DFA result(*walkable);
	delete walkable;
	return result;
}

WalkableDFA *graph_to_dfa(vector<vertex_t> vs, vector<edge_t> es) {
	sort(es.begin(), es.end());
	vector<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) vs_squared.push_back(make_pair(u, v));
	vector<edge_t> es_prime;
	set_difference(vs_squared.begin(), vs_squared.end(), es.begin(), es.end(), inserter(es_prime, es_prime.end()));

	vector<WalkableDFA*> dfas;
	transform(es.begin(), es.end(), inserter(dfas, dfas.end()),
		[&](auto e){
			return new AtomicDFA(edge_to_dfa(e.first, e.second, vs));
		}
		);
	transform(es_prime.begin(), es_prime.end(), inserter(dfas, dfas.end()),
		[&](auto e){
			return new AtomicDFA(exclude_edge_to_dfa(e.first, e.second, vs));
		}
		);
	// random_shuffle(dfas.begin(), dfas.end());
	return dfa_conjunction(dfas);
}

pair<size_t, size_t> dfa_stats(vector<vertex_t> vs, vector<edge_t> es) {
	WalkableDFA *walkable = graph_to_dfa(vs, es);
	DFA dfa(*walkable);
	delete walkable;
	return make_pair(dfa.num_states(), dfa.num_transitions());
}

void run() {
	vector<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F' };
	vector<edge_t> es = {
		{ 'A', 'B' },
		{ 'A', 'C' },
		{ 'A', 'D' },
		{ 'B', 'C' },
		{ 'B', 'E' },
		{ 'C', 'F' },
		{ 'D', 'E' },
		{ 'D', 'F' },
		{ 'E', 'F' },
	};

	// vector<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E' };
	// vector<edge_t> es = {
	// 	{ 'A', 'B' },
	// 	{ 'A', 'C' },
	// 	{ 'A', 'D' },
	// 	{ 'B', 'C' },
	// 	{ 'B', 'E' },
	// 	{ 'D', 'E' },
	// };

	size_t num_states, num_transitions;
	tie(num_states, num_transitions) = dfa_stats(vs, es);

	cout << "num_states = " << num_states << endl;
	cout << "num_transitions = " << num_transitions << endl;
}

int main() {
	run();
}