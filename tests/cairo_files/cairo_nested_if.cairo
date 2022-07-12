func main{}():
	[ap] = 3; ap++

	if [ap-1] == 3:
		[ap] = 10; ap++

		if [ap-1] == 5:
			[ap-2] = 6
		else:
			[ap-2] = 1
		end
	else:
		if [ap-1] == 4:
			[ap-2] = 7
		else:
			[ap-2] = 2
		end
	end
	ret
end