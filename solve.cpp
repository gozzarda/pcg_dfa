#include <bits/stdc++.h>

using namespace std;

typedef uint8_t vertex_t;
typedef pair<vertex_t, vertex_t> edge_t;

typedef uint32_t state_t;
typedef vertex_t event_t;

// struct pair_hash {
// 	template <class T1, class T2>
// 	size_t operator() (const pair<T1, T2> &p) const { return hash<T1>()(p.first) ^ hash<T2>()(p.second); }
// };

struct DFA {
	vector<map<event_t, state_t>> transitions;
	set<state_t> accepting;

	state_t add_state(bool accept = false) {
		state_t result = transitions.size();
		transitions.emplace_back();
		if (accept) accepting.insert(result);
		return result;
	}

	void add_transition(state_t from, event_t event, state_t to) {
		transitions[from][event] = to;
	}

	size_t num_states() const {
		return transitions.size();
	}

	size_t num_transitions() const {
		return accumulate(transitions.begin(), transitions.end(), 0, [](size_t lhs, auto rhs){ return lhs + rhs.size(); });
	}

	set<event_t> alphabet() const {
		set<event_t> result;
		for (auto row : transitions) {
			for (auto kv : row) {
				result.insert(kv.first);
			}
		}
		return result;
	}

	//private
	bool dfs(vector<event_t>& sequence, vector<char>& visited, state_t curr) {
		if (visited[curr]) return false;
		visited[curr] = true;

		if (accepting.count(curr)) return true;

		for (auto kv : transitions[curr]) {
			event_t e = kv.first;
			state_t next = kv.second;
			sequence.push_back(e);
			if (dfs(sequence, visited, next)) return true;
			sequence.pop_back();
		}

		return false;
	}

	pair<bool, vector<event_t>> find_solution() {
		vector<event_t> sequence;
		vector<char> visited(num_states(), false);
		return make_pair(dfs(sequence, visited, 0), sequence);
	}

	DFA operator&&(const DFA &rhs) const {
		const DFA &lhs = *this;
		DFA result;

		map<pair<state_t, state_t>, state_t> compress;

		stack<pair<state_t, state_t>> s;
		s.push(make_pair(0, 0));
		compress.emplace(s.top(), result.add_state(lhs.accepting.count(0) && rhs.accepting.count(0)));

		while (!s.empty()) {
			auto curr = s.top(); s.pop();
			state_t from = compress[curr];
			state_t ls, rs;
			tie(ls, rs) = curr;

			for (auto kv : lhs.transitions[ls]) {
				event_t e = kv.first;
				if (!rhs.transitions[rs].count(e)) continue;
				state_t ln = kv.second;
				state_t rn = rhs.transitions.at(rs).at(e);
				auto n = make_pair(ln, rn);

				if (!compress.count(n)) {
					bool accept = lhs.accepting.count(ln) && rhs.accepting.count(rn);
					compress.emplace(n, result.add_state(accept));
					s.push(n);
				}

				result.transitions[from][e] = compress[n];
			}
		}

		return result;
	}

	// Reduces states that can't possibly reach an accepting state to a single deadend state
	DFA simplify_halting() const {
		vector<vector<state_t>> rev_list(num_states());

		for (int u = 0; u < num_states(); ++u) {
			for (auto kv : transitions[u]) {
				state_t v = kv.second;
				rev_list[v].push_back(u);
			}
		}

		set<state_t> satisfiable = accepting;
		stack<state_t> s;
		for (state_t state : accepting) s.push(state);

		while (!s.empty()) {
			state_t curr = s.top(); s.pop();

			for (state_t next : rev_list[curr]) {
				if (satisfiable.count(next)) continue;
				satisfiable.insert(next);
				s.push(next);
			}
		}

		DFA result;
		map<state_t, state_t> reindex;

		reindex.emplace(0, result.add_state(accepting.count(0)));
		s.push(0);

		while (!s.empty()) {
			state_t curr = s.top(); s.pop();

			for (auto kv : transitions[curr]) {
				event_t e; state_t next;
				tie(e, next) = kv;
				if (!satisfiable.count(next)) continue;
				if (!reindex.count(next)) {
					reindex.emplace(next, result.add_state(accepting.count(next)));
					s.push(next);
				}
				result.add_transition(reindex[curr], e, reindex[next]);
			}
		}

		return result;
	}

	static DFA conjunction(vector<DFA>::iterator lwr, vector<DFA>::iterator upr) {
		if (next(lwr) == upr) return *lwr;
		auto mid = lwr + distance(lwr, upr) / 2;
		return (conjunction(lwr, mid) && conjunction(mid, upr)).simplify_halting();
	}
};

DFA edge_to_dfa_parity(vertex_t u, vertex_t v, const set<vertex_t> &vs) {
	DFA result;
	state_t init = result.add_state();			for (vertex_t v : vs) result.add_transition(init, v, init);
	state_t su = result.add_state();			for (vertex_t v : vs) result.add_transition(su, v, su);
	state_t suv = result.add_state();			for (vertex_t v : vs) result.add_transition(suv, v, suv);
	state_t suvu = result.add_state(true);		for (vertex_t v : vs) result.add_transition(suvu, v, suvu);
	result.add_transition(init, u, su);
	result.add_transition(su, v, suv);
	result.add_transition(suv, u, suvu);
	return result;
}

DFA exclude_edge_to_dfa_parity(vertex_t u, vertex_t v, const set<vertex_t> &vs) {
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

DFA graph_to_dfa(set<vertex_t> vs, set<edge_t> es) {
	for (auto e : es) es.insert(make_pair(e.second, e.first));
	set<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) if (u != v) vs_squared.insert(make_pair(u, v));
	vector<edge_t> es_prime;
	set_difference(vs_squared.begin(), vs_squared.end(), es.begin(), es.end(), inserter(es_prime, es_prime.end()));

	vector<DFA> dfas;
	transform(es.begin(), es.end(), inserter(dfas, dfas.end()),
		[&](auto e){
			return edge_to_dfa_parity(e.first, e.second, vs);
		}
		);
	transform(es_prime.begin(), es_prime.end(), inserter(dfas, dfas.end()),
		[&](auto e){
			return exclude_edge_to_dfa_parity(e.first, e.second, vs);
		}
		);
	random_shuffle(dfas.begin(), dfas.end());	// Avoid expensive structures
	// for (auto lwr = dfas.begin(), upr = prev(dfas.end()); lwr < upr; lwr += 2, upr -= 2) {
	// 	swap(*lwr, *upr);
	// }
	return DFA::conjunction(dfas.begin(), dfas.end());
}

set<edge_t> random_edge_set(set<vertex_t> vs, double density = 0.5) {
	vector<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) if (u < v) vs_squared.push_back(make_pair(u, v));
	random_shuffle(vs_squared.begin(), vs_squared.end());
	auto it = vs_squared.begin();
	int num_edges = round(vs_squared.size() * density);
	set<edge_t> result;
	for (int i = 0; i < num_edges; ++i) result.insert(*it++);
	return result;
}

void run() {
	set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F' };
	set<edge_t> es = {
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

	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E' };
	// set<edge_t> es = {
	// 	{ 'A', 'B' },
	// 	{ 'A', 'C' },
	// 	{ 'A', 'D' },
	// 	{ 'B', 'C' },
	// 	{ 'B', 'E' },
	// 	{ 'D', 'E' },
	// };

	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F' };
	// set<edge_t> es = random_edge_set(vs);

	DFA dfa = graph_to_dfa(vs, es);

	cout << "num_states = " << dfa.num_states() << endl;
	cout << "num_transitions = " << dfa.num_transitions() << endl;

	auto p = dfa.find_solution();
	if (p.first) {
		cout << "Found solution: ";
		for (event_t e : p.second) cout << e;
		cout << endl;
	} else {
		cout << "No solution found" << endl;
	}
}

int main() {
	run();
}