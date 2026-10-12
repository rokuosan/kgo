package main

import "fmt"

func sum(values []int) int {
	total := 0
	for _, value := range values {
		total += value
	}
	return total
}

func main() {
	values := []int{2, 3, 5, 7}
	fmt.Println("values:", values)
	fmt.Println("sum:", sum(values))
}
