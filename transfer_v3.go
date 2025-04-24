package main

import (
	"fmt"
	"math/rand"
	"sync"
	"time"
)

const NumTransfers = 2

type Person string

const (
	Alice Person = "alice"
	Bob   Person = "bob"
)

var People = []Person{Alice, Bob}

// Per-account state
type Account struct {
	sync.Mutex
	balance int
}

type State struct {
	accounts map[Person]*Account
}

func wire(id int, state *State, wg *sync.WaitGroup) {
	defer wg.Done()

	// Random transfer setup
	var from, to Person
	for {
		from = People[rand.Intn(len(People))]
		to = People[rand.Intn(len(People))]
		if from != to {
			break
		}
	}
	amnt := rand.Intn(5) + 1

	// Acquire locks in a consistent order to prevent deadlock
	first, second := from, to
	if from > to {
		first, second = to, from
	}

	state.accounts[first].Lock()
	state.accounts[second].Lock()

	// Critical section: transfer money if possible
	if state.accounts[from].balance >= amnt {
		state.accounts[from].balance -= amnt
		state.accounts[to].balance += amnt
	}

	// Release locks
	state.accounts[second].Unlock()
	state.accounts[first].Unlock()
}

func main() {
	rand.Seed(time.Now().UnixNano())
	for j:=0; j < 1000000; j++ {
		state := &State{
			accounts: map[Person]*Account{
				Alice: {balance: 10},
				Bob:   {balance: 10},
			},
		}

		var wg sync.WaitGroup
		for i := 0; i < NumTransfers; i++ {
			wg.Add(1)
			go wire(i, state, &wg)
		}
		wg.Wait()

		fmt.Println("Final account balances:")
		for _, p := range People {
			fmt.Printf("  %s: %d\n", p, state.accounts[p].balance)
		}
	}
}
