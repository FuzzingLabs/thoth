func main{}():
	[ap] = 3; ap++

#

	if 50 == 3:
		[ap] = [ap-1]; ap++
	else:
		[ap] = 2; ap++
	end

#

	if 50 - [ap-1] == 3:
		[ap] = [ap-1]; ap++
	else:
		[ap] = 2; ap++
	end

#

	if [ap-1] - 50 == 3:
		[ap] = 25; ap++
	else:
		[ap] = 2; ap++
	end

#

	if [ap-1] + 50 == 3:
		[ap] = 25; ap++
	else:
		[ap] = 2; ap++
	end

#

	if 10 + 50 == 3:
		[ap] = 25; ap++
	else:
		[ap] = 2; ap++
	end

#

	if [fp+2] - [ap-6] == 3:
		[ap] = 25; ap++
	else:
		[ap] = 2; ap++
	end

#

	ret
end