func main{}():
	[ap] = 50; ap++

	if [ap-1] == 50:
		[ap] = 25; ap++
		[ap] = 10; ap++
	else:
		[ap] = 2; ap++
	end
	[ap] = [ap-1]
	ret
end