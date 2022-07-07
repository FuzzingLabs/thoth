func main{}():
	[ap] = 3; ap++

	if [ap-1] + 50 == 3:
		[ap] = 25; ap++
		[ap] = 10; ap++
		[ap] = [ap-1]; ap++
		[ap] = [ap-1]; ap++
	else:
		[ap] = 2; ap++
	end
	[ap] = [ap-1]
	ret
end