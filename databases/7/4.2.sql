update Marks
set
	Mark = (
		select nm.Mark
		from NewMarks nm
		where
			nm.StudentId = Marks.StudentId
			and nm.CourseId = Marks.CourseId
	)
where
	exists (
		select nm.Mark
		from NewMarks nm
		where
			nm.StudentId = Marks.StudentId
			and nm.CourseId = Marks.CourseId
	)
