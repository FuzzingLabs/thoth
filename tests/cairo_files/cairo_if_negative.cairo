func main{}():
	[ap] = 3618502788666131213697322783095070105623107215331596699973092056135872020431; ap++

	if - [ap-1] == -1:
		[ap] = 10; ap++

		if [ap-1] == 5:
			[ap] = -6; ap++
		else:
			[ap] = -1; ap++
		end
	else:
		if -1 - [ap-1] == - 4:
			[ap] = -7; ap++
		else:
			[ap] = -2; ap++
		end
	end
	ret
end