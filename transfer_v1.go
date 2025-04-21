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


	if state.accounts[from].balance >= amnt {
		state.accounts[from].balance -= amnt
		state.accounts[to].balance += amnt
	}

}

func main() {
	state := &State{
		accounts: map[Person]*Account{
			Alice: {balance: 10},
			Bob:   {balance: 10},
		},
	}

	for j:=0; j < 3000; j++ {
		rand.Seed(time.Now().UnixNano())

		var wg sync.WaitGroup
		for i := 0; i < NumTransfers; i++ {
			wg.Add(1)
			go wire(i, state, &wg)
		}
		wg.Wait()

		fmt.Println("Final account balances:")
		for _, p := range People {
			fmt.Printf("  %s: %d\n", p, state.accounts[p].balance)
			if state.accounts[p].balance < 0 {
				fmt.Println("ERROR!");
				return
			}
		}
	}
}
