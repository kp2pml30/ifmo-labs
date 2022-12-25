select SessionId
from Sessions
except
select SessionId
from Sessions natural join Problems left join Runs using (SessionId, Letter)
where
	Runs.Accepted is null